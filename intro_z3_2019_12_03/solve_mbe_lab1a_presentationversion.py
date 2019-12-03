import z3
solver = z3.Solver()
wanted_length = 8
assert wanted_length > 5 # checked at 0x08048a4f
sym_username = [z3.BitVec('x{i}'.format(i=i), 8) for i in range(wanted_length)]
sym_serial = z3.BitVec('serial', 32)
# -----
eax = z3.SignExt(24, sym_username[3]) # (int32_t)*((uint8_t*)arg_8h + 3)
eax ^= z3.BitVecVal(0x1337, 32)
eax += z3.BitVecVal(0x5eeded, 32)
local_10h = eax
# -----
local_ch = len(sym_username) # this is set by the strnlen at 0x08048a3e
for local_14h in range(local_ch):
    pass # we'll translate the loop body here
# -----
    solver.add(sym_username[local_14h] > 0x1f)
    # +++
    eax = z3.SignExt(24, sym_username[local_14h])
    eax ^= local_10h
    # +++
    ecx = eax
    edx = z3.BitVecVal(0x88233b2b, 32)
    eax = ecx
# -----
    mul_result = z3.ZeroExt(32, eax) * z3.ZeroExt(32, edx)
    edx = z3.Extract(63, 32, mul_result)
    eax = z3.Extract(31, 0, mul_result)
    # +++
    eax = ecx
    eax -= edx
    eax = eax >> 1
    eax += edx
    eax = eax >> 0xa
    # +++
    eax = z3.Extract(31, 0, z3.SignExt(32, eax) * 0x539)
    # +++
    ecx -= eax
    eax = ecx
    local_10h += eax
# -----
solver.add(sym_serial == local_10h) # outside the loop
solver.push() # backtracking point for next demo
username = 'username'
for (x, y) in zip(username, sym_username):
    solver.add(ord(x) == y)
assert solver.check().r == 1
model = solver.model()
serial = model.evaluate(sym_serial)
print('serial for name %r is %r' % (username, serial))
# -----
solver.pop() # remove the constraints on the provided username
solver.add(sym_serial == serial+1)
assert solver.check().r == 1
model = solver.model()
username2 = ''.join(chr(model.evaluate(x).as_long()) for x in sym_username)
serial2 = model.evaluate(sym_serial)
print('serial for name %r is %r' % (username2, serial2))
