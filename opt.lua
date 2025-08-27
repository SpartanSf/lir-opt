local json = require("json")
local serpent = require("serpent")

local function read_ir(filename)
    local f = io.open(filename, "r")
    if not f then error("cannot open "..filename) end
    local data = json.decode(f:read("*a"))
    f:close()
    return data
end

local function write_ir(ir, filename)
    local f = io.open(filename, "w")
    if not f then error("cannot open for write "..filename) end
    f:write(json.encode(ir))
    f:close()
end

local args = {...}

local opt_passes = {}

if not (#args >= 3) then
    print("opt.lua [source] [dest] [optimizations -ube, -cf, -ms, -lvp, -ssad, -lcp, -pep, -mb, -rucu, OR -all]")
end

local ir = read_ir(args[1])

local original_header = ir.header and { numparams = ir.header.numparams,
    is_vararg = ir.header.is_vararg,
    maxstack = ir.header.maxstack } or nil

local function is_reg_operand(o) return type(o) == "table" and o.kind == "reg" end
local function is_const_operand(o) return type(o) == "table" and o.kind == "const" end
local function is_up_operand(o) return type(o) == "table" and o.kind == "up" end

local function op_lower(instr)
    return (instr.op or ""):lower()
end

local function build_const_index_map(consts)
    local map = {}
    for i,v in ipairs(consts or {}) do
        map[serpent.serialize(v, {compact=true})] = i-1
    end
    return map
end

local function get_or_add_const(ir, val)
    ir.consts = ir.consts or {}
    local key = serpent.serialize(val, {compact=true})
    local map = build_const_index_map(ir.consts)
    if map[key] ~= nil then return map[key] end
    table.insert(ir.consts, val)
    return #ir.consts - 1
end

local function build_def_map(ir)
    local def = {}
    for _, block in ipairs(ir.blocks or {}) do
        for i, instr in ipairs(block.instrs or {}) do
            if instr.dst and type(instr.dst) == "string" then
                def[instr.dst] = { block = block, instr = instr, index = i }
            end
        end
    end
    return def
end

local function build_use_map(ir)
    local uses = {}
    for _, block in ipairs(ir.blocks or {}) do
        for _, instr in ipairs(block.instrs or {}) do
            for opi, op in ipairs(instr.operands or {}) do
                if is_reg_operand(op) then
                    uses[op.name] = uses[op.name] or {}
                    table.insert(uses[op.name], { block = block, instr = instr, idx = opi })
                end
            end
        end
    end
    return uses
end

local function collect_successors(ir)
    local label_to_block = {}
    for _, b in ipairs(ir.blocks or {}) do label_to_block[b.name] = b end
    local succ = {}
    for i, b in ipairs(ir.blocks or {}) do
        succ[b.name] = succ[b.name] or {}
        local nb = ir.blocks[i+1]
        if nb then succ[b.name][nb.name] = true end
        for _, instr in ipairs(b.instrs or {}) do
            if instr.meta then
                for _, k in ipairs({"target","body","loop","loop_target"}) do
                    local tgt = instr.meta[k]
                    if type(tgt) == "string" and label_to_block[tgt] then succ[b.name][tgt] = true end
                end
            end
            for _, op in ipairs(instr.operands or {}) do
                if type(op) == "string" and label_to_block[op] then succ[b.name][op] = true end
            end
        end
    end
    return succ
end

local function ub_elim(ir)
    local succ = collect_successors(ir)
    local entry = (ir.blocks and ir.blocks[1]) and ir.blocks[1].name or nil
    if not entry then return 0 end
    local visited = {}
    local stack = {entry}
    visited[entry] = true
    while #stack > 0 do
        local n = table.remove(stack)
        for tgt,_ in pairs(succ[n] or {}) do
            if not visited[tgt] then visited[tgt] = true; table.insert(stack, tgt) end
        end
    end
    local removed = 0
    local newblocks = {}
    for _, b in ipairs(ir.blocks or {}) do
        if visited[b.name] then table.insert(newblocks, b) else removed = removed + 1 end
    end
    ir.blocks = newblocks
    return removed
end

local function compute_predecessors(ir)
    local preds = {}
    local label_to_block = {}
    for _, b in ipairs(ir.blocks or {}) do label_to_block[b.name] = b; preds[b.name] = preds[b.name] or {} end
    for i, b in ipairs(ir.blocks or {}) do
        local nb = ir.blocks[i+1]
        if nb then preds[nb.name][b.name] = true end
        for _, instr in ipairs(b.instrs or {}) do
            if instr.meta then
                for _, k in ipairs({"target","body","loop","loop_target"}) do
                    local tgt = instr.meta[k]
                    if type(tgt) == "string" and label_to_block[tgt] then preds[tgt][b.name] = true end
                end
            end
            for _, op in ipairs(instr.operands or {}) do
                if type(op) == "string" and label_to_block[op] then preds[op][b.name] = true end
            end
        end
    end
    return preds
end

local function mrg_blocks(ir)
    local preds = compute_predecessors(ir)
    local label_to_index = {}
    for i,b in ipairs(ir.blocks or {}) do label_to_index[b.name] = i end
    local merged = false
    local i = 1
    while i <= #ir.blocks do
        local b = ir.blocks[i]
        local last = (b.instrs and b.instrs[#b.instrs]) or nil
        local target = nil
        if last and last.meta then
            target = last.meta.target or last.meta.body or last.meta.loop or last.meta.loop_target
        end
        if type(target) == "string" and preds[target] then
            local pcount = 0
            for _ in pairs(preds[target]) do pcount = pcount + 1 end
            if pcount == 1 then
                local tgt_idx = label_to_index[target]
                if tgt_idx and tgt_idx > i then
                    local tgt = table.remove(ir.blocks, tgt_idx)
                    for _, instr in ipairs(tgt.instrs or {}) do table.insert(b.instrs, instr) end
                    merged = true
                    preds = compute_predecessors(ir)
                    label_to_index = {}
                    for ii,bb in ipairs(ir.blocks or {}) do label_to_index[bb.name] = ii end
                    goto continue_merge_loop
                end
            end
        end
        i = i + 1
        ::continue_merge_loop::
    end
    return merged and 1 or 0
end

local function eval_binary(op, a, b)
    if op == "add" then return a + b end
    if op == "sub" then return a - b end
    if op == "mul" then return a * b end
    if op == "div" then return a / b end
    if op == "mod" then return a % b end
    return nil
end

local function const_fold(ir)
    local replaced = 0
    ir.consts = ir.consts or {}
    for _, block in ipairs(ir.blocks or {}) do
        for i, instr in ipairs(block.instrs or {}) do
            local o = op_lower(instr)
            if (o == "add" or o == "sub" or o == "mul" or o == "div" or o == "mod") and instr.operands and #instr.operands >= 2 then
                local a = instr.operands[1]
                local b = instr.operands[2]
                if is_const_operand(a) and is_const_operand(b) then
                    local aval = ir.consts[a.idx+1]
                    local bval = ir.consts[b.idx+1]
                    if type(aval) == "number" and type(bval) == "number" then
                        local ok, res = pcall(eval_binary, o, aval, bval)
                        if ok and res ~= nil then
                            local kidx = get_or_add_const(ir, res)
                            instr.op = "const"
                            instr.operands = { { kind = "const", idx = kidx } }
                            replaced = replaced + 1
                        end
                    end
                end
            end
        end
    end
    return replaced
end

local function math_simplify(ir)
    local changed = 0
    ir.consts = ir.consts or {}
    for _, block in ipairs(ir.blocks or {}) do
        for _, instr in ipairs(block.instrs or {}) do
            local o = op_lower(instr)
            if (o == "add" or o == "sub" or o == "mul" or o == "div") and instr.operands and #instr.operands >= 2 then
                local a = instr.operands[1]
                local b = instr.operands[2]
                local function const_val(op)
                    if is_const_operand(op) then return ir.consts[op.idx+1] end
                    return nil
                end
                local av = const_val(a)
                local bv = const_val(b)
                if o == "add" then
                    if bv == 0 then
                        instr.op = "move"
                        instr.operands = { a }
                        changed = changed + 1
                    elseif av == 0 then
                        instr.op = "move"
                        instr.operands = { b }
                        changed = changed + 1
                    end
                elseif o == "sub" then
                    if bv == 0 then
                        instr.op = "move"
                        instr.operands = { a }
                        changed = changed + 1
                    elseif av == 0 and is_reg_operand(b) then
                        local kidx = get_or_add_const(ir, -1)
                        instr.op = "mul"
                        instr.operands = { { kind = "const", idx = kidx }, b }
                        changed = changed + 1
                    end
                elseif o == "mul" then
                    if bv == 1 then instr.op = "move"; instr.operands = { a }; changed = changed + 1
                    elseif av == 1 then instr.op = "move"; instr.operands = { b }; changed = changed + 1
                    elseif bv == 0 or av == 0 then
                        local kidx = get_or_add_const(ir, 0)
                        instr.op = "const"
                        instr.operands = { { kind = "const", idx = kidx } }
                        changed = changed + 1
                    end
                elseif o == "div" then
                    if bv == 1 then instr.op = "move"; instr.operands = { a }; changed = changed + 1 end
                end
            end
        end
    end
    return changed
end

local function peephole_block(block, ir)
    local removed = 0
    local i = 1
    while i <= #block.instrs do
        local instr = block.instrs[i]
        if instr.op == "const" then
            local nexti = i + 1
            local n = block.instrs[nexti]
            if n and n.op == "move" and n.operands and #n.operands >= 1 then
                local srcop = n.operands[1]
                if is_reg_operand(srcop) and srcop.name == instr.dst then
                    local constop = instr.operands and instr.operands[1]
                    if is_const_operand(constop) then
                        n.op = "const"
                        n.operands = { { kind = "const", idx = constop.idx } }
                        removed = removed + 0
                    end
                end
            end
        end
        i = i + 1
    end
    return removed
end

local function peephole_pass(ir)
    local tot = 0
    for _, b in ipairs(ir.blocks or {}) do tot = tot + peephole_block(b, ir) end
    return tot
end

local function lc_prop(ir)
    local changed = 0
    for _, b in ipairs(ir.blocks or {}) do
        local mapping = {}
        local newinstrs = {}
        for _, instr in ipairs(b.instrs or {}) do
            if instr.op == "move" and instr.operands and is_reg_operand(instr.operands[1]) and instr.dst then
                local srcname = instr.operands[1].name
                mapping[instr.dst] = mapping[srcname] or srcname
                changed = changed + 1
            else
                if instr.operands then
                    for i, op in ipairs(instr.operands) do
                        if is_reg_operand(op) and mapping[op.name] then
                            instr.operands[i] = { kind = "reg", name = mapping[op.name] }
                        end
                    end
                end
                table.insert(newinstrs, instr)
            end
        end
        b.instrs = newinstrs
    end
    return changed
end

local function lvn_block(block)
    local valnum = {}
    local reg2val = {}

    local function key_of_operand(op)
        if is_const_operand(op) then
            return "K"..tostring(op.idx)
        elseif is_up_operand(op) then
            return "U"..tostring(op.idx)
        elseif is_reg_operand(op) then
            local rn = reg2val[op.name]
            if rn then return rn end
            return "R:"..op.name
        else
            return tostring(op)
        end
    end

    local new_instrs = {}
    local removed = 0

    for _, instr in ipairs(block.instrs or {}) do
        local op_low = (instr.op or ""):lower()

        if instr.dst and instr.operands then
            local parts = { op_low }
            for i, op in ipairs(instr.operands) do table.insert(parts, key_of_operand(op)) end
            local key = table.concat(parts, "|")

            if valnum[key] then
                local rep = valnum[key]
                reg2val[instr.dst] = (is_reg_operand(rep) and ("R:"..rep.name)) or ("K"..tostring(rep.idx))
                removed = removed + 1
            else
                for i, op in ipairs(instr.operands) do
                    if is_reg_operand(op) then
                        local mapped = reg2val[op.name]
                        if mapped and mapped:sub(1,2) == "R:" then
                            local newname = mapped:sub(3)
                            instr.operands[i] = { kind = "reg", name = newname }
                        elseif mapped and mapped:sub(1,1) == "K" then
                            local kidx = tonumber(mapped:sub(2))
                            instr.operands[i] = { kind = "const", idx = kidx }
                        end
                    end
                end
                valnum[key] = { kind = "reg", name = instr.dst }
                reg2val[instr.dst] = "R:" .. instr.dst
                table.insert(new_instrs, instr)
            end
        else
            table.insert(new_instrs, instr)
        end
    end

    block.instrs = new_instrs
    return removed
end

local function lvn_pass(ir)
    local total_removed = 0
    for _, b in ipairs(ir.blocks or {}) do total_removed = total_removed + lvn_block(b) end
    return total_removed
end

local function instr_uses(instr)
    if instr.operands then
        local uses = {}
        local op = (instr.op or ""):lower()
        for _, o in ipairs(instr.operands or {}) do
            if type(o) == "table" and o.kind == "reg" then table.insert(uses, o.name) end
        end
        return uses
    end
    local uses = {}
    local function add(x) if type(x) == "string" then table.insert(uses, x) end end
    if instr.src then add(instr.src) end
    if instr.idx then add(instr.idx) end
    if instr.func then add(instr.func) end
    if instr.args then for _, a in ipairs(instr.args) do if type(a) == "string" then add(a) end end end
    return uses
end

local function is_pure_instr(instr)
    local op = (instr.op or ""):lower()
    local impure = { call = true, forprep = true, forloop = true, ret = true, ["return"] = true, settable = true, settabup = true }
    return not impure[op]
end

local function ssa_dce(ir)
    local def = build_def_map(ir)
    local live = {}
    local queue = {}

    for _, block in ipairs(ir.blocks or {}) do
        for _, instr in ipairs(block.instrs or {}) do
            local op_low = (instr.op or ""):lower()
            if op_low == "ret" or op_low == "return" then
                for _, op in ipairs(instr.operands or {}) do if is_reg_operand(op) and not live[op.name] then live[op.name] = true; table.insert(queue, op.name) end end
            end
            if not is_pure_instr(instr) then
                for _, op in ipairs(instr.operands or {}) do if is_reg_operand(op) and not live[op.name] then live[op.name] = true; table.insert(queue, op.name) end end
            end
        end
    end

    while #queue > 0 do
        local r = table.remove(queue)
        local info = def[r]
        if info and info.instr then
            for _, u in ipairs(instr_uses(info.instr)) do
                if not live[u] then live[u] = true; table.insert(queue, u) end
            end
        end
    end

    local removed = 0
    for _, block in ipairs(ir.blocks or {}) do
        local newinstr = {}
        for _, instr in ipairs(block.instrs or {}) do
            if instr.dst and type(instr.dst) == "string" then
                if not live[instr.dst] and is_pure_instr(instr) then
                    removed = removed + 1
                else
                    table.insert(newinstr, instr)
                end
            else
                table.insert(newinstr, instr)
            end
        end
        block.instrs = newinstr
    end
    return removed
end

function remove_ucu(proto)
    local used_consts = {}
    local used_upvals = {}

    for _, block in ipairs(proto.blocks or {}) do
        for _, ins in ipairs(block.instrs or {}) do
            if ins.operands then
                for _, op in ipairs(ins.operands) do
                    if op.kind == "const" then
                        used_consts[op.idx] = true
                    elseif is_up_operand(op) then
                        used_upvals[op.idx] = true
                    end
                end
            end
        end
    end

    local old_consts = proto.consts or {}
    local new_consts = {}
    local const_remap = {}
    for one_based_idx, c in ipairs(old_consts) do
        local old_zero = one_based_idx - 1
        if used_consts[old_zero] then
            table.insert(new_consts, c)
            const_remap[old_zero] = #new_consts - 1
        end
    end
    proto.consts = new_consts

    local old_upvals = proto.upvalues or {}
    local new_upvals = {}
    local upval_remap = {}
    for one_based_idx, u in ipairs(old_upvals) do
        local old_zero = one_based_idx - 1
        if used_upvals[old_zero] then
            table.insert(new_upvals, u)
            upval_remap[old_zero] = #new_upvals - 1
        end
    end
    proto.upvalues = new_upvals

    for _, block in ipairs(proto.blocks or {}) do
        for _, ins in ipairs(block.instrs or {}) do
            if ins.operands then
                for _, op in ipairs(ins.operands) do
                    if op.kind == "const" then
                        local new_idx = const_remap[op.idx]
                        if new_idx == nil then
                            error("Internal optimizer error: const-instr refers to removed const (old idx="..tostring(op.idx)..")")
                        end
                        op.idx = new_idx
                    elseif is_up_operand(op) then
                        local new_idx = upval_remap[op.idx]
                        if new_idx == nil then
                            error("Internal optimizer error: upval-instr refers to removed upval (old idx="..tostring(op.idx)..")")
                        end
                        op.idx = new_idx
                    end
                end
            end
        end
    end

    local removed_consts = #old_consts - #new_consts
    local removed_upvals = #old_upvals - #new_upvals
    return removed_consts + removed_upvals
end

local function validate_and_fix_ir(ir)
    ir.header = ir.header or original_header or { numparams = 0, is_vararg = 1, maxstack = 8 }

    ir.consts = ir.consts or {}
    ir.upvalues = ir.upvalues or {}

    for _, b in ipairs(ir.blocks or {}) do
        for _, instr in ipairs(b.instrs or {}) do
            for _, op in ipairs(instr.operands or {}) do
                if is_const_operand(op) then
                    if type(op.idx) ~= "number" or op.idx < 0 or (op.idx+1) > #ir.consts then
                        error(("IR validation failed: operand const idx out of bounds (%s)"):format(tostring(op.idx)))
                    end
                end
                if is_up_operand(op) then
                end
            end
        end
    end
    return true
end

local opt_passes_funcs = {
    ube  = ub_elim,
    cf   = const_fold,
    ms   = math_simplify,
    lvp  = lvn_pass,
    ssad = ssa_dce,
    lcp  = lc_prop,
    pep  = peephole_pass,
    mb   = mrg_blocks,
    rucu = remove_ucu,
}

local all_mode = false
for i = 3, #args do
    if args[i] == "-all" then
        all_mode = true
    else
        local name = args[i]:sub(2)
        if opt_passes_funcs[name] then
            opt_passes[name] = true
        end
    end
end

if all_mode then
    for name in pairs(opt_passes_funcs) do
        opt_passes[name] = true
    end
end

local function optimize(ir)
    if not ir or not ir.blocks then return end

    local changed = true
    local iter = 0
    while changed and iter < 10 do
        iter = iter + 1
        changed = false

        for name, func in pairs(opt_passes_funcs) do
            if opt_passes[name] then
                local n = func(ir)
                changed = changed or (n and n > 0)
            end
        end
    end
end

local before_instrs = 0
for _, b in ipairs(ir.blocks or {}) do before_instrs = before_instrs + (#b.instrs or 0) end

optimize(ir)
validate_and_fix_ir(ir)

local after_instrs = 0
for _, b in ipairs(ir.blocks or {}) do after_instrs = after_instrs + (#b.instrs or 0) end

print(string.format("Optimization iterations complete. Instrs before: %d, after: %d", before_instrs, after_instrs))

write_ir(ir, args[2])
