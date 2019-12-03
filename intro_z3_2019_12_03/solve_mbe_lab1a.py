import z3

'''
|     ||`-> 0x08048ab6      8b4508         movl arg_8h, %eax           ; [0x8:4]=-1 ; 8
|     ||    0x08048ab9      83c003         addl $3, %eax
|     ||    0x08048abc      0fb600         movzbl 0(%eax), %eax
|     ||    0x08048abf      0fbec0         movsbl %al, %eax
|     ||    0x08048ac2      3537130000     xorl $0x1337, %eax
|     ||    0x08048ac7      05eded5e00     addl $0x5eeded, %eax
|     ||    0x08048acc      8945f0         movl %eax, local_10h
|     ||    0x08048acf      c745ec000000.  movl $0, local_14h
|     ||,=< 0x08048ad6      eb4e           jmp 0x8048b26
|    .----> 0x08048ad8      8b55ec         movl local_14h, %edx
|    :|||   0x08048adb      8b4508         movl arg_8h, %eax           ; [0x8:4]=-1 ; 8
|    :|||   0x08048ade      01d0           addl %edx, %eax
|    :|||   0x08048ae0      0fb600         movzbl 0(%eax), %eax
|    :|||   0x08048ae3      3c1f           cmpb $0x1f, %al             ; 31
|   ,=====< 0x08048ae5      7f07           jg 0x8048aee
|   |:|||   0x08048ae7      b801000000     movl $1, %eax
|  ,======< 0x08048aec      eb54           jmp 0x8048b42
|  |`-----> 0x08048aee      8b55ec         movl local_14h, %edx
|  | :|||   0x08048af1      8b4508         movl arg_8h, %eax           ; [0x8:4]=-1 ; 8
|  | :|||   0x08048af4      01d0           addl %edx, %eax
|  | :|||   0x08048af6      0fb600         movzbl 0(%eax), %eax
|  | :|||   0x08048af9      0fbec0         movsbl %al, %eax
|  | :|||   0x08048afc      3345f0         xorl local_10h, %eax
|  | :|||   0x08048aff      89c1           movl %eax, %ecx
|  | :|||   0x08048b01      ba2b3b2388     movl $0x88233b2b, %edx
|  | :|||   0x08048b06      89c8           movl %ecx, %eax
|  | :|||   0x08048b08      f7e2           mull %edx
|  | :|||   0x08048b0a      89c8           movl %ecx, %eax
|  | :|||   0x08048b0c      29d0           subl %edx, %eax
|  | :|||   0x08048b0e      d1e8           shrl $1, %eax
|  | :|||   0x08048b10      01d0           addl %edx, %eax
|  | :|||   0x08048b12      c1e80a         shrl $0xa, %eax
|  | :|||   0x08048b15      69c039050000   imull $0x539, %eax, %eax
|  | :|||   0x08048b1b      29c1           subl %eax, %ecx
|  | :|||   0x08048b1d      89c8           movl %ecx, %eax
|  | :|||   0x08048b1f      0145f0         addl %eax, local_10h
|  | :|||   0x08048b22      8345ec01       addl $1, local_14h
|  | :|||   ; CODE XREF from sym.auth (0x8048ad6)
|  | :||`-> 0x08048b26      8b45ec         movl local_14h, %eax
|  | :||    0x08048b29      3b45f4         cmpl local_ch, %eax
|  | `====< 0x08048b2c      7caa           jl 0x8048ad8
|  |  ||    0x08048b2e      8b450c         movl arg_ch, %eax           ; [0xc:4]=-1 ; 12
|  |  ||    0x08048b31      3b45f0         cmpl local_10h, %eax
|  |  ||,=< 0x08048b34      7407           je 0x8048b3d
|  |  |||   0x08048b36      b801000000     movl $1, %eax
|  | ,====< 0x08048b3b      eb05           jmp 0x8048b42
|  | |||`-> 0x08048b3d      b800000000     movl $0, %eax
|  | |||    ; CODE XREFS from sym.auth (0x8048a5a, 0x8048ab1, 0x8048aec, 0x8048b3b)
|  `-```--> 0x08048b42      c9             leave
\           0x08048b43      c3             retl
'''

# username is fgets'd at 0x08048bc9
# serial is scanf('%u')'d at 0x08048c19
def find_serial(solver, username, serial, model=None):
    local_ch = len(username) # required to be > 5 at 0x08048a4f - 0x08048a5a
    assert local_ch > 5

    # 0x08048abf - 0x08048acc
    local_10h = z3.SignExt(24, username[3])
    local_10h ^= z3.BitVecVal(0x1337, 32)
    local_10h += z3.BitVecVal(0x5eeded, 32)
    if model:
        print('after xor and add: %r' % (model.evaluate(local_10h),))

    for local_14h in range(local_ch):
        solver.add(username[local_14h] > 0x1f) # 0x08048ae3 - 0x08048ae5
        eax = local_10h ^ z3.SignExt(24, username[local_14h]) # 0x08048aee - 0x08048afc
        ecx = eax # 0x08048aff
        edx = z3.BitVecVal(0x88233b2b, 32) # 0x08048b01
        eax = ecx
        #mul_result = z3.Int2BV(z3.BV2Int(eax) * z3.BV2Int(edx), 64)
        #mul_result = z3.SignExt(32, eax) * z3.SignExt(32, edx)
        mul_result = z3.ZeroExt(32, eax) * z3.ZeroExt(32, edx)
        edx = z3.Extract(63, 32, mul_result)
        eax = z3.Extract(31, 0, mul_result)
        eax = ecx
        eax -= edx
        eax = eax >> 1
        #eax = z3.LShR(eax, 1)
        eax += edx
        eax = eax >> 0xa
        #eax = z3.LShR(eax, 0xa)
        eax = z3.Extract(31, 0, z3.SignExt(32, eax) * 0x539)
        ecx -= eax
        eax = ecx
        local_10h += eax
        if model:
            print(model.evaluate(eax), model.evaluate(edx), model.evaluate(local_10h))

    solver.add(serial == local_10h)
    return local_10h

def serial_given_username(username):
    solver = z3.Solver()
    #username = 'username'
    #username = '_'*8
    sym_username = [z3.BitVec('x{i}'.format(i=i), 8) for (i, _) in enumerate(username)]
    sym_serial = z3.BitVec('serial', 32)
    for (x, y) in zip(username, sym_username):
        solver.add(ord(x) == y)
    computed_serial = find_serial(solver, sym_username, sym_serial)
    if solver.check().r == 1:
        model = solver.model()
        print('serial for name %r is %r' % (username, model.evaluate(computed_serial),))
        return sym_username, sym_serial, model

def username_given_serial(serial, length):
    solver = z3.Solver()
    sym_username = [z3.BitVec('x%d' % (i,), 8) for i in range(length)]
    sym_serial = z3.BitVec('serial', 32)
    solver.add(sym_serial == serial)
    computed_serial = find_serial(solver, sym_username, sym_serial)
    if solver.check().r == 1:
        model = solver.model()
        username = ''.join(chr(model.evaluate(x).as_long()) for x in sym_username)
        print('serial for name %r is %r' % (username, model.evaluate(computed_serial),))
        return sym_username, sym_serial, model

import time
print(time.time())
user1, ser1, mod1 = serial_given_username('username')
print(time.time())
user2, ser2, mod2 = serial_given_username('propernoun')
print(time.time())
user3, ser3, mod3 = username_given_serial(mod1.evaluate(ser1)-1, len(user1))
print(time.time())
user4, ser4, mod4 = username_given_serial(mod1.evaluate(ser1), len(user1))
print(time.time())
user5, ser5, mod5 = username_given_serial(mod1.evaluate(ser1)+1, len(user1))
print(time.time())

# z3.BitVecRef(z3.Z3_mk_zero_ext(x.ctx.ref(), 1, x.ast))
#('username', 6234463) via gdb + patch
