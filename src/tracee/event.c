/* -*- c-set-style: "K&R"; c-basic-offset: 8 -*-
 *
 * This file is part of PRoot.
 *
 * Copyright (C) 2015 STMicroelectronics
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA.
 */

#include <stdio.h>
#include <sched.h>      /* CLONE_*,  */
#include <sys/types.h>  /* pid_t, */
#include <sys/ptrace.h> /* ptrace(1), PTRACE_*, */
#include <sys/types.h>  /* waitpid(2), */
#include <sys/wait.h>   /* waitpid(2), */
#include <sys/utsname.h> /* uname(2), */
#include <unistd.h>     /* fork(2), chdir(2), getpid(2), */
#include <string.h>     /* strcmp(3), */
#include <errno.h>      /* errno(3), */
#include <stdbool.h>    /* bool, true, false, */
#include <assert.h>     /* assert(3), */
#include <stdlib.h>     /* atexit(3), getenv(3), */
#include <talloc.h>     /* talloc_*, */
#include <inttypes.h>   /* PRI*, */
#include <linux/version.h> /* KERNEL_VERSION, */
#include <sys/user.h>   /* struct user_regs_struct, */

#include "tracee/event.h"
#include "cli/note.h"
#include "path/path.h"
#include "path/binding.h"
#include "syscall/syscall.h"
#include "syscall/seccomp.h"
#include "ptrace/wait.h"
#include "extension/extension.h"
#include "execve/elf.h"

#include "attribute.h"
#include "compat.h"

#ifdef HAVE_LIBDW
#include <elfutils/libdwfl.h>
#include <dwarf.h>
#endif

#if defined(ARCH_ARM64)
#include <linux/elf.h>  /* NT_PRSTATUS */
#endif

#define STACK_TRACE_MAX_FRAMES 32

/**
 * Look up the address in /proc/<pid>/maps and format a short
 * description ("pathname+offset") into @buf of size @buf_size.
 * Returns @buf for convenience.
 */
static const char *maps_lookup(pid_t pid, unsigned long addr,
				char *buf, size_t buf_size)
{
	char maps_path[64];
	FILE *f;
	unsigned long start, end;
	char line[512];

	snprintf(maps_path, sizeof(maps_path), "/proc/%d/maps", (int) pid);
	f = fopen(maps_path, "r");
	if (f == NULL) {
		snprintf(buf, buf_size, "??");
		return buf;
	}

	while (fgets(line, sizeof(line), f) != NULL) {
		char perms[8];
		unsigned long offset;
		unsigned int dev_maj, dev_min;
		unsigned long inode;
		char pathname[256];
		int n;

		n = sscanf(line, "%lx-%lx %7s %lx %x:%x %lu %255s",
			&start, &end, perms, &offset,
			&dev_maj, &dev_min, &inode, pathname);

		if (n < 7)
			continue;

		if (addr >= start && addr < end) {
			const char *name = (n >= 8) ? pathname : "[anonymous]";
			snprintf(buf, buf_size, "%s+0x%lx",
				name, addr - start + offset);
			fclose(f);
			return buf;
		}
	}

	fclose(f);
	snprintf(buf, buf_size, "??");
	return buf;
}

/**
 * Read a word from the tracee's memory at @address using ptrace.
 * Returns 0 and sets @value on success, -1 on error.
 */
static int peek_tracee_word(pid_t pid, unsigned long address,
			unsigned long *value)
{
	long result;

	errno = 0;
	result = ptrace(PTRACE_PEEKDATA, pid, (void *) address, NULL);
	if (errno != 0)
		return -1;

	*value = (unsigned long) result;
	return 0;
}

#ifdef HAVE_LIBDW

/* DWARF x86_64 register numbers for parameter-passing registers */
#if defined(ARCH_X86_64)
#define DWARF_REG_TO_PTRACE(n, regs) dwarf_x86_64_reg(n, regs)
static unsigned long dwarf_x86_64_reg(unsigned int regnum,
					const struct user_regs_struct *regs)
{
	switch (regnum) {
	case  0: return (unsigned long) regs->rax;
	case  1: return (unsigned long) regs->rdx;
	case  2: return (unsigned long) regs->rcx;
	case  3: return (unsigned long) regs->rbx;
	case  4: return (unsigned long) regs->rsi;
	case  5: return (unsigned long) regs->rdi;
	case  6: return (unsigned long) regs->rbp;
	case  7: return (unsigned long) regs->rsp;
	case  8: return (unsigned long) regs->r8;
	case  9: return (unsigned long) regs->r9;
	case 10: return (unsigned long) regs->r10;
	case 11: return (unsigned long) regs->r11;
	case 12: return (unsigned long) regs->r12;
	case 13: return (unsigned long) regs->r13;
	case 14: return (unsigned long) regs->r14;
	case 15: return (unsigned long) regs->r15;
	default: return 0;
	}
}
#elif defined(ARCH_X86)
#define DWARF_REG_TO_PTRACE(n, regs) dwarf_x86_reg(n, regs)
static unsigned long dwarf_x86_reg(unsigned int regnum,
				const struct user_regs_struct *regs)
{
	switch (regnum) {
	case 0: return (unsigned long) regs->eax;
	case 1: return (unsigned long) regs->ecx;
	case 2: return (unsigned long) regs->edx;
	case 3: return (unsigned long) regs->ebx;
	case 4: return (unsigned long) regs->esp;
	case 5: return (unsigned long) regs->ebp;
	case 6: return (unsigned long) regs->esi;
	case 7: return (unsigned long) regs->edi;
	default: return 0;
	}
}
#elif defined(ARCH_ARM_EABI)
#define DWARF_REG_TO_PTRACE(n, regs) ((unsigned long)(regs)->uregs[(n) < 16 ? (n) : 0])
#elif defined(ARCH_ARM64)
#define DWARF_REG_TO_PTRACE(n, regs) ((unsigned long)(regs)->regs[(n) < 31 ? (n) : 0])
#else
#define DWARF_REG_TO_PTRACE(n, regs) ((void)(n), (void)(regs), 0UL)
#endif

/*
 * Number of bytes added to the frame pointer to get the CFA
 * (Canonical Frame Address) for a function with a standard prologue.
 * CFA is the stack pointer value at the call instruction.
 */
#if defined(ARCH_X86_64) || defined(ARCH_ARM64)
#define CFA_FP_OFFSET 16UL
#elif defined(ARCH_X86)
#define CFA_FP_OFFSET 8UL
#elif defined(ARCH_ARM_EABI)
/* ARM EABI frame: FP points to [saved_PC, saved_SP, saved_LR, saved_FP] at -4/-8/-12 */
#define CFA_FP_OFFSET 0UL
#else
#define CFA_FP_OFFSET 0UL
#endif

/**
 * Resolve a DWARF type DIE to its underlying base type, skipping
 * typedef / const / volatile / restrict wrappers.
 * Returns false if the type could not be resolved.
 */
static bool resolve_type(Dwarf_Die *type_die, Dwarf_Die *result)
{
	Dwarf_Die tmp = *type_die;
	int depth = 0;

	while (depth++ < 16) {
		int tag = dwarf_tag(&tmp);

		if (tag == DW_TAG_base_type || tag == DW_TAG_pointer_type ||
		    tag == DW_TAG_enumeration_type)
			break;

		if (tag == DW_TAG_typedef || tag == DW_TAG_const_type ||
		    tag == DW_TAG_volatile_type ||
		    tag == DW_TAG_restrict_type) {
			Dwarf_Attribute attr;
			Dwarf_Die next;

			if (dwarf_attr(&tmp, DW_AT_type, &attr) == NULL)
				return false;
			if (dwarf_formref_die(&attr, &next) == NULL)
				return false;
			tmp = next;
		} else {
			break;
		}
	}

	*result = tmp;
	return true;
}

/**
 * Read a value of @byte_size bytes from the tracee's memory or
 * a register and store it as an unsigned long.
 */
static bool read_value(pid_t pid, unsigned long addr, unsigned int byte_size,
			unsigned long *out)
{
	unsigned long word = 0;
	unsigned int i;
	uint8_t bytes[8];

	if (byte_size > sizeof(bytes))
		byte_size = sizeof(bytes);

	for (i = 0; i < byte_size; i += sizeof(unsigned long)) {
		unsigned long w;
		if (peek_tracee_word(pid, addr + i, &w) < 0)
			return false;
		memcpy(&bytes[i], &w,
			(byte_size - i < sizeof(unsigned long))
			? (byte_size - i) : sizeof(unsigned long));
	}

	word = 0;
	memcpy(&word, bytes, byte_size);
	*out = word;
	return true;
}

/**
 * Evaluate a simple DWARF location expression for a parameter.
 * @fp        frame pointer for the frame containing the parameter
 * @regs      register values (only valid for frame 0, may be NULL for others)
 * @expr      the location expression
 * @exprlen   length of the expression
 * @addr_out  the computed address (for memory-based locations)
 * @reg_val   the register value (for register-based locations)
 * @is_reg    set to true if the result is a register value, not an address
 *
 * Returns true on success.
 */
static bool eval_location(unsigned long fp,
			const struct user_regs_struct *regs,
			const Dwarf_Op *expr, size_t exprlen,
			unsigned long *addr_out, unsigned long *reg_val,
			bool *is_reg)
{
	const Dwarf_Op *op;
	unsigned long cfa;

	if (exprlen == 0)
		return false;

	op = &expr[0];
	*is_reg = false;
	cfa = fp + CFA_FP_OFFSET;

	switch (op->atom) {
	case DW_OP_fbreg:
		/* frame_base + signed offset; assume frame_base = CFA */
		*addr_out = cfa + (unsigned long)(long) op->number;
		return true;

	case DW_OP_addr:
		*addr_out = (unsigned long) op->number;
		return true;
	}

	/* DW_OP_reg0..DW_OP_reg31: value is in a register */
	if (op->atom >= DW_OP_reg0 && op->atom <= DW_OP_reg31) {
		if (regs == NULL)
			return false;
		*reg_val = DWARF_REG_TO_PTRACE(op->atom - DW_OP_reg0, regs);
		*is_reg  = true;
		return true;
	}

	/* DW_OP_bregN (DW_OP_breg0..DW_OP_breg31): register N + signed LEB128 offset */
	if (op->atom >= DW_OP_breg0 && op->atom <= DW_OP_breg0 + 31) {
		if (regs == NULL)
			return false;
		unsigned int regnum = op->atom - DW_OP_breg0;
		unsigned long base  = DWARF_REG_TO_PTRACE(regnum, regs);
		*addr_out = base + (unsigned long)(long) op->number;
		return true;
	}

	return false;
}

/**
 * Format a value of the given DWARF type into @buf.
 */
static void format_value(pid_t pid, unsigned long val, bool is_addr,
			Dwarf_Die *type_die, char *buf, size_t buf_size)
{
	Dwarf_Die base;
	int tag;
	Dwarf_Word byte_size = 0;
	Dwarf_Attribute attr;

	if (!resolve_type(type_die, &base)) {
		snprintf(buf, buf_size, "0x%lx", val);
		return;
	}

	tag = dwarf_tag(&base);

	if (tag == DW_TAG_pointer_type) {
		/* For char pointers, try to print as string */
		Dwarf_Attribute type_attr;
		Dwarf_Die pointee;

		snprintf(buf, buf_size, "0x%lx", val);

		if (val != 0 &&
		    dwarf_attr(&base, DW_AT_type, &type_attr) != NULL &&
		    dwarf_formref_die(&type_attr, &pointee) != NULL) {
			Dwarf_Die pointee_base;
			if (resolve_type(&pointee, &pointee_base) &&
			    dwarf_tag(&pointee_base) == DW_TAG_base_type) {
				Dwarf_Word enc = 0;
				Dwarf_Attribute enc_attr;
				if (dwarf_attr(&pointee_base, DW_AT_encoding,
						&enc_attr) != NULL)
					dwarf_formudata(&enc_attr, &enc);
				if (enc == DW_ATE_signed_char ||
				    enc == DW_ATE_unsigned_char) {
					/* Read up to 32 bytes of string */
					char str[33];
					unsigned int i;
					bool ok = true;
					for (i = 0; i < sizeof(str) - 1; i++) {
						unsigned long b = 0;
						if (!read_value(pid, val + i,
								1, &b)) {
							ok = false;
							break;
						}
						if (b == 0)
							break;
						str[i] = (char) b;
					}
					str[i] = '\0';
					if (ok && i > 0) {
						/* Buffer: max 16 hex digits for
						 * address + ' "' + str + '"' or
						 * '"..."' + NUL */
						char tmp[18 + sizeof(str) + 5];
						snprintf(tmp, sizeof(tmp),
							"0x%lx \"%s%s\"",
							val, str,
							i == sizeof(str) - 1
							? "..." : "");
						snprintf(buf, buf_size, "%s",
							tmp);
					}
				}
			}
		}
		return;
	}

	if (tag == DW_TAG_base_type) {
		Dwarf_Word enc = 0;

		if (dwarf_attr(&base, DW_AT_byte_size, &attr) != NULL)
			dwarf_formudata(&attr, &byte_size);
		if (dwarf_attr(&base, DW_AT_encoding, &attr) != NULL)
			dwarf_formudata(&attr, &enc);

		/* Sign-extend if needed */
		if (enc == DW_ATE_signed && byte_size > 0 &&
		    byte_size < sizeof(unsigned long)) {
			unsigned int shift = (unsigned int)
					(8 * (sizeof(unsigned long) - byte_size));
			long sval = ((long)(val << shift)) >> shift;
			snprintf(buf, buf_size, "%ld", sval);
		} else if (enc == DW_ATE_signed) {
			snprintf(buf, buf_size, "%ld", (long) val);
		} else if (enc == DW_ATE_boolean) {
			snprintf(buf, buf_size, "%s", val ? "true" : "false");
		} else {
			snprintf(buf, buf_size, "%lu", val);
		}
		return;
	}

	if (tag == DW_TAG_enumeration_type) {
		/* Find the enumerator whose value matches */
		Dwarf_Die child;
		if (dwarf_child(&base, &child) == 0) {
			do {
				if (dwarf_tag(&child) != DW_TAG_enumerator)
					continue;
				Dwarf_Attribute cval_attr;
				Dwarf_Word cval = 0;
				if (dwarf_attr(&child, DW_AT_const_value,
						&cval_attr) != NULL &&
				    dwarf_formudata(&cval_attr, &cval) == 0 &&
				    cval == val) {
					Dwarf_Attribute name_attr;
					const char *name;
					if (dwarf_attr(&child, DW_AT_name,
							&name_attr) != NULL &&
					    (name = dwarf_formstring(
							&name_attr)) != NULL) {
						snprintf(buf, buf_size,
							"%s (%lu)", name, val);
						return;
					}
				}
			} while (dwarf_siblingof(&child, &child) == 0);
		}
		snprintf(buf, buf_size, "%lu", val);
		return;
	}

	(void) is_addr;
	snprintf(buf, buf_size, "0x%lx", val);
}

/**
 * Print all formal parameters for a function at @pc with the given
 * frame pointer @fp.  @regs is the full register set for frame 0
 * (may be NULL for other frames).
 */
static void print_frame_params(const Tracee *tracee, Dwfl_Module *mod,
				Dwarf_Addr pc, unsigned long fp,
				const struct user_regs_struct *regs,
				Dwarf_Addr bias)
{
	Dwarf_Die *scopes = NULL;
	Dwarf_Die *cudie;
	int nscopes, i;
	bool first = true;
	char line_buf[512];
	int pos = 0;

	cudie = dwfl_module_addrdie(mod, pc, &bias);
	if (cudie == NULL)
		return;

	/* Get the scope chain at this PC (relative to the CU bias) */
	nscopes = dwarf_getscopes(cudie, pc - bias, &scopes);
	if (nscopes <= 0)
		return;

	/* scopes[0] is the innermost scope; find the DW_TAG_subprogram */
	for (i = 0; i < nscopes; i++) {
		Dwarf_Die child;

		if (dwarf_tag(&scopes[i]) != DW_TAG_subprogram)
			continue;

		/* Iterate children looking for formal parameters */
		if (dwarf_child(&scopes[i], &child) != 0)
			break;

		do {
			Dwarf_Attribute name_attr, loc_attr, type_attr;
			const char *pname;
			Dwarf_Op *expr;
			size_t exprlen;
			Dwarf_Die type_die;
			unsigned long addr_val = 0, reg_val = 0;
			bool is_reg = false;
			char val_buf[128];

			if (dwarf_tag(&child) != DW_TAG_formal_parameter)
				continue;

			if (dwarf_attr(&child, DW_AT_name, &name_attr) == NULL)
				continue;
			pname = dwarf_formstring(&name_attr);
			if (pname == NULL)
				continue;

			/* Get the type, for formatting the value */
			if (dwarf_attr(&child, DW_AT_type, &type_attr) == NULL
			    || dwarf_formref_die(&type_attr, &type_die)
				== NULL) {
				if (!first)
					pos += snprintf(line_buf + pos,
						sizeof(line_buf) - pos, ", ");
				pos += snprintf(line_buf + pos,
					sizeof(line_buf) - pos, "%s=?",
					pname);
				first = false;
				continue;
			}

			/* Evaluate the parameter's location expression */
			if (dwarf_attr(&child, DW_AT_location,
					&loc_attr) == NULL ||
			    dwarf_getlocation_addr(&loc_attr,
					(Dwarf_Addr)(pc - bias),
					&expr, &exprlen, 1) <= 0 ||
			    exprlen == 0 ||
			    !eval_location(fp, regs, expr, exprlen,
					&addr_val, &reg_val, &is_reg)) {
				/* No location: parameter might be optimized */
				Dwarf_Word byte_size = 0;
				Dwarf_Attribute sz_attr;
				Dwarf_Die base;
				if (resolve_type(&type_die, &base) &&
				    dwarf_attr(&base, DW_AT_byte_size,
						&sz_attr) != NULL)
					dwarf_formudata(&sz_attr, &byte_size);

				if (!first)
					pos += snprintf(line_buf + pos,
						sizeof(line_buf) - pos, ", ");
				pos += snprintf(line_buf + pos,
					sizeof(line_buf) - pos,
					"%s=<optimized out>", pname);
				first = false;
				continue;
			}

			/* Read the value from memory or register */
			val_buf[0] = '\0';
			if (is_reg) {
				format_value(tracee->pid, reg_val, false,
						&type_die, val_buf,
						sizeof(val_buf));
			} else {
				Dwarf_Die base;
				Dwarf_Attribute sz_attr;
				Dwarf_Word byte_size = sizeof(unsigned long);
				unsigned long raw_val = 0;

				if (resolve_type(&type_die, &base)) {
					if (dwarf_tag(&base) ==
					    DW_TAG_pointer_type)
						byte_size = sizeof(void *);
					else if (dwarf_attr(&base,
							DW_AT_byte_size,
							&sz_attr) != NULL)
						dwarf_formudata(&sz_attr,
							&byte_size);
				}

				if (read_value(tracee->pid, addr_val,
						(unsigned int) byte_size,
						&raw_val))
					format_value(tracee->pid, raw_val,
						false, &type_die, val_buf,
						sizeof(val_buf));
				else
					snprintf(val_buf, sizeof(val_buf),
						"<unreadable>");
			}

			if (!first)
				pos += snprintf(line_buf + pos,
					sizeof(line_buf) - pos, ", ");
			pos += snprintf(line_buf + pos,
				sizeof(line_buf) - pos, "%s=%s",
				pname, val_buf);
			first = false;
		} while (dwarf_siblingof(&child, &child) == 0 &&
			(size_t) pos < sizeof(line_buf) - 4);

		break;
	}

	free(scopes);

	if (!first)
		VERBOSE(tracee, 1, "vpid %" PRIu64 ":      (%s)",
			tracee->vpid, line_buf);
}

#endif /* HAVE_LIBDW */

/**
 * Print a stack trace for the given @tracee using its current register
 * state (read via ptrace).  Only printed when verbose level >= 1.
 * This should be called while the tracee is stopped (e.g., at
 * PTRACE_EVENT_EXIT) so that its registers and memory are still
 * accessible.
 */
static void print_stack_trace(Tracee *tracee)
{
	struct user_regs_struct regs;
	unsigned long pc, sp, fp;
	char info[512];
	int frame;

	if (tracee->verbose < 1)
		return;

#if defined(ARCH_ARM64)
	{
		struct iovec iov;
		iov.iov_base = &regs;
		iov.iov_len  = sizeof(regs);
		if (ptrace(PTRACE_GETREGSET, tracee->pid,
				(void *)(long) NT_PRSTATUS, &iov) < 0)
			return;
		pc = (unsigned long) regs.pc;
		sp = (unsigned long) regs.sp;
		fp = (unsigned long) regs.regs[29]; /* X29 */
	}
#else
	if (ptrace(PTRACE_GETREGS, tracee->pid, NULL, &regs) < 0)
		return;

# if defined(ARCH_X86_64)
	pc = (unsigned long) regs.rip;
	sp = (unsigned long) regs.rsp;
	fp = (unsigned long) regs.rbp;
# elif defined(ARCH_X86)
	pc = (unsigned long) regs.eip;
	sp = (unsigned long) regs.esp;
	fp = (unsigned long) regs.ebp;
# elif defined(ARCH_ARM_EABI)
	pc = (unsigned long) regs.uregs[15]; /* PC */
	sp = (unsigned long) regs.uregs[13]; /* SP */
	fp = (unsigned long) regs.uregs[11]; /* R11/FP */
# elif defined(ARCH_SH4)
	pc = (unsigned long) regs.pc;
	sp = (unsigned long) regs.regs[15];
	fp = 0; /* SH4 has no dedicated frame pointer */
# else
	(void) regs;
	return;
# endif
#endif

	(void) sp;

#ifdef HAVE_LIBDW
	{
	static const Dwfl_Callbacks proc_callbacks = {
		.find_elf       = dwfl_linux_proc_find_elf,
		.find_debuginfo = dwfl_standard_find_debuginfo,
		.debuginfo_path = NULL,
	};
	Dwfl *dwfl = dwfl_begin(&proc_callbacks);
	if (dwfl != NULL) {
		dwfl_linux_proc_report(dwfl, tracee->pid);
		dwfl_report_end(dwfl, NULL, NULL);
	}

	VERBOSE(tracee, 1, "vpid %" PRIu64 ": stack trace:", tracee->vpid);

	/* Frame 0: the instruction pointer at the time of signal termination.  */
	{
		Dwfl_Module *mod0 = dwfl ? dwfl_addrmodule(dwfl, pc) : NULL;
		const char *func0 = NULL;
		GElf_Off func0_off = 0;

		if (mod0) {
			GElf_Sym sym;
			func0 = dwfl_module_addrinfo(mod0, pc, &func0_off,
						&sym, NULL, NULL, NULL);
		}

		if (func0) {
			Dwfl_Line *ln = dwfl_module_getsrc(mod0, pc);
			const char *src = NULL;
			int lineno = 0, col = 0;
			if (ln)
				src = dwfl_lineinfo(ln, NULL, &lineno, &col,
						NULL, NULL);
			if (src && lineno > 0)
				VERBOSE(tracee, 1,
					"vpid %" PRIu64
					":  #%-2d 0x%0*lx  %s()"
					" at %s:%d",
					tracee->vpid, 0,
					(int)(2 * sizeof(unsigned long)), pc,
					func0, src, lineno);
			else
				VERBOSE(tracee, 1,
					"vpid %" PRIu64
					":  #%-2d 0x%0*lx  %s()",
					tracee->vpid, 0,
					(int)(2 * sizeof(unsigned long)), pc,
					func0);

			if (mod0) {
				Dwarf_Addr bias = 0;
				print_frame_params(tracee, mod0, (Dwarf_Addr)pc,
						fp, &regs, bias);
			}
		} else {
			VERBOSE(tracee, 1,
				"vpid %" PRIu64 ":  #%-2d 0x%0*lx  %s",
				tracee->vpid, 0,
				(int)(2 * sizeof(unsigned long)), pc,
				maps_lookup(tracee->pid, pc, info,
						sizeof(info)));
		}
	}

	/* Walk the frame-pointer chain to collect return addresses.  */
	for (frame = 1; frame < STACK_TRACE_MAX_FRAMES && fp != 0; frame++) {
		unsigned long ret_addr = 0;
		unsigned long prev_fp  = 0;
		int word_size;

#if defined(ARCH_X86_64) || defined(ARCH_ARM64)
		word_size = 8;
#else
		word_size = 4;
#endif

#if defined(ARCH_ARM_EABI)
		if (peek_tracee_word(tracee->pid, fp - 4, &ret_addr) < 0)
			break;
		if (peek_tracee_word(tracee->pid, fp - 8, &prev_fp) < 0)
			break;
#else
		if (peek_tracee_word(tracee->pid, fp, &prev_fp) < 0)
			break;
		if (peek_tracee_word(tracee->pid,
				fp + (unsigned long) word_size,
				&ret_addr) < 0)
			break;
#endif

		if (ret_addr == 0)
			break;

		{
		Dwfl_Module *mod = dwfl
			? dwfl_addrmodule(dwfl, ret_addr) : NULL;
		const char *func = NULL;
		GElf_Off func_off = 0;

		if (mod) {
			GElf_Sym sym;
			func = dwfl_module_addrinfo(mod, ret_addr, &func_off,
						&sym, NULL, NULL, NULL);
		}

		if (func) {
			Dwfl_Line *ln = dwfl_module_getsrc(mod, ret_addr);
			const char *src = NULL;
			int lineno = 0, col = 0;
			if (ln)
				src = dwfl_lineinfo(ln, NULL, &lineno, &col,
						NULL, NULL);
			if (src && lineno > 0)
				VERBOSE(tracee, 1,
					"vpid %" PRIu64
					":  #%-2d 0x%0*lx  %s()"
					" at %s:%d",
					tracee->vpid, frame,
					(int)(2 * sizeof(unsigned long)),
					ret_addr, func, src, lineno);
			else
				VERBOSE(tracee, 1,
					"vpid %" PRIu64
					":  #%-2d 0x%0*lx  %s()",
					tracee->vpid, frame,
					(int)(2 * sizeof(unsigned long)),
					ret_addr, func);

			if (mod) {
				Dwarf_Addr bias = 0;
				/* The function at ret_addr belongs to the
				 * caller's frame whose FP is prev_fp.  */
				print_frame_params(tracee, mod,
					(Dwarf_Addr) ret_addr, prev_fp,
					NULL, bias);
			}
		} else {
			VERBOSE(tracee, 1,
				"vpid %" PRIu64 ":  #%-2d 0x%0*lx  %s",
				tracee->vpid, frame,
				(int)(2 * sizeof(unsigned long)), ret_addr,
				maps_lookup(tracee->pid, ret_addr, info,
						sizeof(info)));
		}
		}

		/* Sanity check: the previous FP must be at a higher address
		 * than the current FP (stack grows downward, so unwinding
		 * moves toward higher addresses) and be reasonably aligned.  */
		if (prev_fp == 0 || prev_fp == fp)
			break;
		if (prev_fp < fp)
			break;
		if (prev_fp % sizeof(unsigned long) != 0)
			break;

		fp = prev_fp;
	}

	if (dwfl)
		dwfl_end(dwfl);
	}
#else  /* !HAVE_LIBDW */

	VERBOSE(tracee, 1, "vpid %" PRIu64 ": stack trace:", tracee->vpid);

	/* Frame 0: the instruction pointer at the time of signal termination.  */
	VERBOSE(tracee, 1, "vpid %" PRIu64 ":  #%-2d 0x%0*lx  %s",
		tracee->vpid, 0,
		(int)(2 * sizeof(unsigned long)), pc,
		maps_lookup(tracee->pid, pc, info, sizeof(info)));

	/* Walk the frame-pointer chain to collect return addresses.  */
	for (frame = 1; frame < STACK_TRACE_MAX_FRAMES && fp != 0; frame++) {
		unsigned long ret_addr = 0;
		unsigned long prev_fp  = 0;
		int word_size;

#if defined(ARCH_X86_64) || defined(ARCH_ARM64)
		word_size = 8;
#else
		word_size = 4;
#endif

#if defined(ARCH_ARM_EABI)
		if (peek_tracee_word(tracee->pid, fp - 4, &ret_addr) < 0)
			break;
		if (peek_tracee_word(tracee->pid, fp - 8, &prev_fp) < 0)
			break;
#else
		if (peek_tracee_word(tracee->pid, fp, &prev_fp) < 0)
			break;
		if (peek_tracee_word(tracee->pid,
				fp + (unsigned long) word_size,
				&ret_addr) < 0)
			break;
#endif

		if (ret_addr == 0)
			break;

		VERBOSE(tracee, 1, "vpid %" PRIu64 ":  #%-2d 0x%0*lx  %s",
			tracee->vpid, frame,
			(int)(2 * sizeof(unsigned long)), ret_addr,
			maps_lookup(tracee->pid, ret_addr, info,
					sizeof(info)));

		/* Sanity check: the previous FP must be at a higher address
		 * than the current FP (stack grows downward, so unwinding
		 * moves toward higher addresses) and be reasonably aligned.  */
		if (prev_fp == 0 || prev_fp == fp)
			break;
		if (prev_fp < fp)
			break;
		if (prev_fp % sizeof(unsigned long) != 0)
			break;

		fp = prev_fp;
	}
#endif /* HAVE_LIBDW */
}


/**
 * Start @tracee->exe with the given @argv[].  This function
 * returns -errno if an error occurred, otherwise 0.
 */
int launch_process(Tracee *tracee, char *const argv[])
{
	char *const default_argv[] = { "-sh", NULL };
	long status;
	pid_t pid;

	/* Warn about open file descriptors. They won't be
	 * translated until they are closed. */
	list_open_fd(tracee);

	pid = fork();
	switch(pid) {
	case -1:
		note(tracee, ERROR, SYSTEM, "fork()");
		return -errno;

	case 0: /* child */
		/* Declare myself as ptraceable before executing the
		 * requested program. */
		status = ptrace(PTRACE_TRACEME, 0, NULL, NULL);
		if (status < 0) {
			note(tracee, ERROR, SYSTEM, "ptrace(TRACEME)");
			return -errno;
		}

		/* Synchronize with the tracer's event loop.  Without
		 * this trick the tracer only sees the "return" from
		 * the next execve(2) so PRoot wouldn't handle the
		 * interpreter/runner.  I also verified that strace
		 * does the same thing. */
		kill(getpid(), SIGSTOP);

		/* Improve performance by using seccomp mode 2, unless
		 * this support is explicitly disabled.  */
		if (getenv("PROOT_NO_SECCOMP") == NULL)
			(void) enable_syscall_filtering(tracee);

		/* Now process is ptraced, so the current rootfs is already the
		 * guest rootfs.  Note: Valgrind can't handle execve(2) on
		 * "foreign" binaries (ENOEXEC) but can handle execvp(3) on such
		 * binaries.  */
		execvp(tracee->exe, argv[0] != NULL ? argv : default_argv);
		return -errno;

	default: /* parent */
		/* We know the pid of the first tracee now.  */
		tracee->pid = pid;
		return 0;
	}

	/* Never reached.  */
	return -ENOSYS;
}

/* Send the KILL signal to all tracees when PRoot has received a fatal
 * signal.  */
static void kill_all_tracees2(int signum, siginfo_t *siginfo UNUSED, void *ucontext UNUSED)
{
	note(NULL, WARNING, INTERNAL, "signal %d received from process %d",
		signum, siginfo->si_pid);
	kill_all_tracees();

	/* Exit immediately for system signals (segmentation fault,
	 * illegal instruction, ...), otherwise exit cleanly through
	 * the event loop.  */
	if (signum != SIGQUIT)
		_exit(EXIT_FAILURE);
}

/**
 * Helper for print_talloc_hierarchy().
 */
static void print_talloc_chunk(const void *ptr, int depth, int max_depth UNUSED,
			int is_ref, void *data UNUSED)
{
	const char *name;
	size_t count;
	size_t size;

	name = talloc_get_name(ptr);
	size = talloc_get_size(ptr);
	count = talloc_reference_count(ptr);

	if (depth == 0)
		return;

	while (depth-- > 1)
		fprintf(stderr, "\t");

	fprintf(stderr, "%-16s ", name);

	if (is_ref)
		fprintf(stderr, "-> %-8p", ptr);
	else {
		fprintf(stderr, "%-8p  %zd bytes  %zd ref'", ptr, size, count);

		if (name[0] == '$') {
			fprintf(stderr, "\t(\"%s\")", (char *)ptr);
		}
		if (name[0] == '@') {
			char **argv;
			int i;

			fprintf(stderr, "\t(");
			for (i = 0, argv = (char **)ptr; argv[i] != NULL; i++)
				fprintf(stderr, "\"%s\", ", argv[i]);
			fprintf(stderr, ")");
		}
		else if (strcmp(name, "Tracee") == 0) {
			fprintf(stderr, "\t(pid = %d, parent = %p)",
				((Tracee *)ptr)->pid, ((Tracee *)ptr)->parent);
		}
		else if (strcmp(name, "Bindings") == 0) {
			Tracee *tracee;

			tracee = TRACEE(ptr);

			if (ptr == tracee->fs->bindings.pending)
				fprintf(stderr, "\t(pending)");
			else if (ptr == tracee->fs->bindings.guest)
				fprintf(stderr, "\t(guest)");
			else if (ptr == tracee->fs->bindings.host)
				fprintf(stderr, "\t(host)");
		}
		else if (strcmp(name, "Binding") == 0) {
			Binding *binding = (Binding *)ptr;
			fprintf(stderr, "\t(%s:%s)", binding->host.path, binding->guest.path);
		}
	}

	fprintf(stderr, "\n");
}

/* Print on stderr the complete talloc hierarchy.  */
static void print_talloc_hierarchy(int signum, siginfo_t *siginfo UNUSED, void *ucontext UNUSED)
{
	switch (signum) {
	case SIGUSR1:
		talloc_report_depth_cb(NULL, 0, 100, print_talloc_chunk, NULL);
		break;

	case SIGUSR2:
		talloc_report_depth_file(NULL, 0, 100, stderr);
		break;

	default:
		break;
	}
}

static int last_exit_status = -1;

/**
 * Check if kernel >= 4.8
 */
static bool is_kernel_4_8(void)
{
	static int version_48 = -1;
	int major = 0;
	int minor = 0;

	if (version_48 != -1)
		return version_48;

	version_48 = false;

	struct utsname utsname;

	if (uname(&utsname) < 0)
		return false;

	sscanf(utsname.release, "%d.%d", &major, &minor);

	if ((major == 4 && minor >= 8) || major > 4)
		version_48 = true;

	return version_48;
}

/**
 * Check if this instance of PRoot can *technically* handle @tracee.
 */
static void check_architecture(Tracee *tracee)
{
	struct utsname utsname;
	ElfHeader elf_header;
	char path[PATH_MAX];
	int status;

	if (tracee->exe == NULL)
		return;

	status = translate_path(tracee, path, AT_FDCWD, tracee->exe, false);
	if (status < 0)
		return;

	status = open_elf(path, &elf_header);
	if (status < 0)
		return;
	close(status);

	if (!IS_CLASS64(elf_header) || sizeof(word_t) == sizeof(uint64_t))
		return;

	note(tracee, ERROR, USER,
		"'%s' is a 64-bit program whereas this version of "
		"%s handles 32-bit programs only", path, tracee->tool_name);

	status = uname(&utsname);
	if (status < 0)
		return;

	if (strcmp(utsname.machine, "x86_64") != 0)
		return;

	note(tracee, INFO, USER,
		"A 64-bit version that supports 32-bit binaries is required");
}

/**
 * Wait then handle any event from any tracee.  This function returns
 * the exit status of the last terminated program.
 */
int event_loop()
{
	struct sigaction signal_action;
	long status;
	int signum;

	/* Kill all tracees when exiting.  */
	status = atexit(kill_all_tracees);
	if (status != 0)
		note(NULL, WARNING, INTERNAL, "atexit() failed");

	/* All signals are blocked when the signal handler is called.
	 * SIGINFO is used to know which process has signaled us and
	 * RESTART is used to restart waitpid(2) seamlessly.  */
	bzero(&signal_action, sizeof(signal_action));
	signal_action.sa_flags = SA_SIGINFO | SA_RESTART;
	status = sigfillset(&signal_action.sa_mask);
	if (status < 0)
		note(NULL, WARNING, SYSTEM, "sigfillset()");

	/* Handle all signals.  */
	for (signum = 0; signum < SIGRTMAX; signum++) {
		switch (signum) {
		case SIGQUIT:
		case SIGILL:
		case SIGABRT:
		case SIGFPE:
		case SIGSEGV:
			/* Kill all tracees on abnormal termination
			 * signals.  This ensures no process is left
			 * untraced.  */
			signal_action.sa_sigaction = kill_all_tracees2;
			break;

		case SIGUSR1:
		case SIGUSR2:
			/* Print on stderr the complete talloc
			 * hierarchy, useful for debug purpose.  */
			signal_action.sa_sigaction = print_talloc_hierarchy;
			break;

		case SIGCHLD:
		case SIGCONT:
		case SIGSTOP:
		case SIGTSTP:
		case SIGTTIN:
		case SIGTTOU:
			/* The default action is OK for these signals,
			 * they are related to tty and job control.  */
			continue;

		default:
			/* Ignore all other signals, including
			 * terminating ones (^C for instance). */
			signal_action.sa_sigaction = (void *)SIG_IGN;
			break;
		}

		status = sigaction(signum, &signal_action, NULL);
		if (status < 0 && errno != EINVAL)
			note(NULL, WARNING, SYSTEM, "sigaction(%d)", signum);
	}

	while (1) {
		int tracee_status;
		Tracee *tracee;
		int signal;
		pid_t pid;

		/* This is the only safe place to free tracees.  */
		free_terminated_tracees();

		/* Wait for the next tracee's stop. */
		pid = waitpid(-1, &tracee_status, __WALL);
		if (pid < 0) {
			if (errno != ECHILD) {
				note(NULL, ERROR, SYSTEM, "waitpid()");
				return EXIT_FAILURE;
			}
			break;
		}

		/* Get information about this tracee. */
		tracee = get_tracee(NULL, pid, true);
		assert(tracee != NULL);

		tracee->running = false;

		VERBOSE(tracee, 6, "vpid %" PRIu64 ": got event %x",
			tracee->vpid, tracee_status);

		status = notify_extensions(tracee, NEW_STATUS, tracee_status, 0);
		if (status != 0)
			continue;

		if (tracee->as_ptracee.ptracer != NULL) {
			bool keep_stopped = handle_ptracee_event(tracee, tracee_status);
			if (keep_stopped)
				continue;
		}

		signal = handle_tracee_event(tracee, tracee_status);
		(void) restart_tracee(tracee, signal);
	}

	return last_exit_status;
}

/**
 * For kernels >= 4.8.0
 * Handle the current event (@tracee_status) of the given @tracee.
 * This function returns the "computed" signal that should be used to
 * restart the given @tracee.
 */
static int handle_tracee_event_kernel_4_8(Tracee *tracee, int tracee_status)
{
	static bool seccomp_detected = false;
	static bool seccomp_enabled = false; /* added for 4.8.0 */
	long status;
	int signal;

	/* Don't overwrite restart_how if it is explicitly set
	 * elsewhere, i.e in the ptrace emulation when single
	 * stepping.  */
	if (tracee->restart_how == 0) {
		/* When seccomp is enabled, all events are restarted in
		 * non-stop mode, but this default choice could be overwritten
		 * later if necessary.  The check against "sysexit_pending"
		 * ensures PTRACE_SYSCALL (used to hit the exit stage under
		 * seccomp) is not cleared due to an event that would happen
		 * before the exit stage, eg. PTRACE_EVENT_EXEC for the exit
		 * stage of execve(2).  */
		if (tracee->seccomp == ENABLED && !tracee->sysexit_pending)
			tracee->restart_how = PTRACE_CONT;
		else
			tracee->restart_how = PTRACE_SYSCALL;
	}

	/* Not a signal-stop by default.  */
	signal = 0;

	if (WIFEXITED(tracee_status)) {
		int exit_status = WEXITSTATUS(tracee_status);
		VERBOSE(tracee, 1,
			"vpid %" PRIu64 ": exited with status %d",
			tracee->vpid, exit_status);
		terminate_tracee(tracee);
		// Avoid overwriting a failure exit code with a success
		if ((exit_status != 0) || (last_exit_status < 0))
			last_exit_status = exit_status;
	}
	else if (WIFSIGNALED(tracee_status)) {
		last_exit_status = 128 + WTERMSIG(tracee_status);
		check_architecture(tracee);
		VERBOSE(tracee, 1,
			"vpid %" PRIu64 ": terminated with signal %d",
			tracee->vpid, WTERMSIG(tracee_status));
		terminate_tracee(tracee);
	}
	else if (WIFSTOPPED(tracee_status)) {
		/* Don't use WSTOPSIG() to extract the signal
		 * since it clears the PTRACE_EVENT_* bits. */
		signal = (tracee_status & 0xfff00) >> 8;

		switch (signal) {
			static bool deliver_sigtrap = false;

		case SIGTRAP: {
			const unsigned long default_ptrace_options = (
				PTRACE_O_TRACESYSGOOD	|
				PTRACE_O_TRACEFORK	|
				PTRACE_O_TRACEVFORK	|
				PTRACE_O_TRACEVFORKDONE	|
				PTRACE_O_TRACEEXEC	|
				PTRACE_O_TRACECLONE	|
				PTRACE_O_TRACEEXIT);

			/* Distinguish some events from others and
			 * automatically trace each new process with
			 * the same options.
			 *
			 * Note that only the first bare SIGTRAP is
			 * related to the tracing loop, others SIGTRAP
			 * carry tracing information because of
			 * TRACE*FORK/CLONE/EXEC.  */
			if (deliver_sigtrap)
				break;  /* Deliver this signal as-is.  */

			deliver_sigtrap = true;

			/* Try to enable seccomp mode 2...  */
			status = ptrace(PTRACE_SETOPTIONS, tracee->pid, NULL,
					default_ptrace_options | PTRACE_O_TRACESECCOMP);
			if (status < 0) {
				seccomp_enabled = false;
				/* ... otherwise use default options only.  */
				status = ptrace(PTRACE_SETOPTIONS, tracee->pid, NULL,
						default_ptrace_options);
				if (status < 0) {
					note(tracee, ERROR, SYSTEM, "ptrace(PTRACE_SETOPTIONS)");
					exit(EXIT_FAILURE);
				}
			}
			else {
				if (getenv("PROOT_NO_SECCOMP") == NULL)
					seccomp_enabled = true;
			}
		}
			/* Fall through. */
		case SIGTRAP | PTRACE_EVENT_SECCOMP2 << 8:
		case SIGTRAP | PTRACE_EVENT_SECCOMP << 8:

			if (!seccomp_detected && seccomp_enabled) {
				VERBOSE(tracee, 1, "ptrace acceleration (seccomp mode 2) enabled");
				tracee->seccomp = ENABLED;
				seccomp_detected = true;
			}

			if (signal == (SIGTRAP | PTRACE_EVENT_SECCOMP2 << 8) ||
			    signal == (SIGTRAP | PTRACE_EVENT_SECCOMP << 8)) {

				unsigned long flags = 0;
				signal = 0;

				/* Use the common ptrace flow if seccomp was
				 * explicitly disabled for this tracee.  */
				if (tracee->seccomp != ENABLED)
					break;

				status = ptrace(PTRACE_GETEVENTMSG, tracee->pid, NULL, &flags);
				if (status < 0)
					break;

				if ((flags & FILTER_SYSEXIT) == 0) {
					tracee->restart_how = PTRACE_CONT;
					translate_syscall(tracee);

					if (tracee->seccomp == DISABLING)
						tracee->restart_how = PTRACE_SYSCALL;
					break;
				}
			}

			/* Fall through. */
		case SIGTRAP | 0x80:

			signal = 0;

			/* This tracee got signaled then freed during the
			   sysenter stage but the kernel reports the sysexit
			   stage; just discard this spurious tracee/event.  */

			if (tracee->exe == NULL) {
				tracee->restart_how = PTRACE_CONT; /* SYSCALL OR CONT */
				return 0;
			}

			switch (tracee->seccomp) {
			case ENABLED:
				if (IS_IN_SYSENTER(tracee)) {
					/* sysenter: ensure the sysexit
					 * stage will be hit under seccomp.  */
					tracee->restart_how = PTRACE_SYSCALL;
					tracee->sysexit_pending = true;
				}
				else {
					/* sysexit: the next sysenter
					 * will be notified by seccomp.  */
					tracee->restart_how = PTRACE_CONT;
					tracee->sysexit_pending = false;
				}
				/* Fall through.  */
			case DISABLED:
				translate_syscall(tracee);

				/* This syscall has disabled seccomp.  */
				if (tracee->seccomp == DISABLING) {
					tracee->restart_how = PTRACE_SYSCALL;
					tracee->seccomp = DISABLED;
				}

				break;

			case DISABLING:
				/* Seccomp was disabled by the
				 * previous syscall, but its sysenter
				 * stage was already handled.  */
				tracee->seccomp = DISABLED;
				if (IS_IN_SYSENTER(tracee))
					tracee->status = 1;
				break;
			}
			break;

		case SIGTRAP | PTRACE_EVENT_VFORK << 8:
			signal = 0;
			(void) new_child(tracee, CLONE_VFORK);
			break;

		case SIGTRAP | PTRACE_EVENT_FORK  << 8:
		case SIGTRAP | PTRACE_EVENT_CLONE << 8:
			signal = 0;
			(void) new_child(tracee, 0);
			break;

		case SIGTRAP | PTRACE_EVENT_VFORK_DONE << 8:
		case SIGTRAP | PTRACE_EVENT_EXEC  << 8:
			signal = 0;
			break;

		case SIGTRAP | PTRACE_EVENT_EXIT  << 8: {
			unsigned long pending_status = 0;
			signal = 0;
			if (ptrace(PTRACE_GETEVENTMSG, tracee->pid, NULL,
					&pending_status) == 0 &&
			    WIFSIGNALED((int) pending_status))
				print_stack_trace(tracee);
			break;
		}

		case SIGSTOP:
			/* Stop this tracee until PRoot has received
			 * the EVENT_*FORK|CLONE notification.  */
			if (tracee->exe == NULL) {
				tracee->sigstop = SIGSTOP_PENDING;
				signal = -1;
			}

			/* For each tracee, the first SIGSTOP
			 * is only used to notify the tracer.  */
			if (tracee->sigstop == SIGSTOP_IGNORED) {
				tracee->sigstop = SIGSTOP_ALLOWED;
				signal = 0;
			}
			break;

		default:
			/* Deliver this signal as-is.  */
			break;
		}
	}

	/* Clear the pending event, if any.  */
	tracee->as_ptracee.event4.proot.pending = false;

	return signal;
}


/**
 * For kernels < 4.8.0
 * Handle the current event (@tracee_status) of the given @tracee.
 * This function returns the "computed" signal that should be used to
 * restart the given @tracee.
 */
int handle_tracee_event(Tracee *tracee, int tracee_status)
{
	static bool seccomp_detected = false;
	long status;
	int signal;

	if (is_kernel_4_8())
		return handle_tracee_event_kernel_4_8(tracee, tracee_status);
	/* Don't overwrite restart_how if it is explicitly set
	 * elsewhere, i.e in the ptrace emulation when single
	 * stepping.  */
	if (tracee->restart_how == 0) {
		/* When seccomp is enabled, all events are restarted in
		 * non-stop mode, but this default choice could be overwritten
		 * later if necessary.  The check against "sysexit_pending"
		 * ensures PTRACE_SYSCALL (used to hit the exit stage under
		 * seccomp) is not cleared due to an event that would happen
		 * before the exit stage, eg. PTRACE_EVENT_EXEC for the exit
		 * stage of execve(2).  */
		if (tracee->seccomp == ENABLED && !tracee->sysexit_pending)
			tracee->restart_how = PTRACE_CONT;
		else
			tracee->restart_how = PTRACE_SYSCALL;
	}

	/* Not a signal-stop by default.  */
	signal = 0;

	if (WIFEXITED(tracee_status)) {
		int exit_status = WEXITSTATUS(tracee_status);
		VERBOSE(tracee, 1,
			"vpid %" PRIu64 ": exited with status %d",
			tracee->vpid, exit_status);
		terminate_tracee(tracee);
		// Avoid overwriting a failure exit code with a success
		if ((exit_status != 0) || (last_exit_status < 0))
			last_exit_status = exit_status;
	}
	else if (WIFSIGNALED(tracee_status)) {
		last_exit_status = 128 + WTERMSIG(tracee_status);
		check_architecture(tracee);
		VERBOSE(tracee, 1,
			"vpid %" PRIu64 ": terminated with signal %d",
			tracee->vpid, WTERMSIG(tracee_status));
		terminate_tracee(tracee);
	}
	else if (WIFSTOPPED(tracee_status)) {
		/* Don't use WSTOPSIG() to extract the signal
		 * since it clears the PTRACE_EVENT_* bits. */
		signal = (tracee_status & 0xfff00) >> 8;

		switch (signal) {
			static bool deliver_sigtrap = false;

		case SIGTRAP: {
			const unsigned long default_ptrace_options = (
				PTRACE_O_TRACESYSGOOD	|
				PTRACE_O_TRACEFORK	|
				PTRACE_O_TRACEVFORK	|
				PTRACE_O_TRACEVFORKDONE	|
				PTRACE_O_TRACEEXEC	|
				PTRACE_O_TRACECLONE	|
				PTRACE_O_TRACEEXIT);

			/* Distinguish some events from others and
			 * automatically trace each new process with
			 * the same options.
			 *
			 * Note that only the first bare SIGTRAP is
			 * related to the tracing loop, others SIGTRAP
			 * carry tracing information because of
			 * TRACE*FORK/CLONE/EXEC.  */
			if (deliver_sigtrap)
				break;  /* Deliver this signal as-is.  */

			deliver_sigtrap = true;

			/* Try to enable seccomp mode 2...  */
			status = ptrace(PTRACE_SETOPTIONS, tracee->pid, NULL,
					default_ptrace_options | PTRACE_O_TRACESECCOMP);
			if (status < 0) {
				/* ... otherwise use default options only.  */
				status = ptrace(PTRACE_SETOPTIONS, tracee->pid, NULL,
						default_ptrace_options);
				if (status < 0) {
					note(tracee, ERROR, SYSTEM, "ptrace(PTRACE_SETOPTIONS)");
					exit(EXIT_FAILURE);
				}
			}
		}

			/* Fall through. */
		case SIGTRAP | 0x80:
			signal = 0;

			/* This tracee got signaled then freed during the
			   sysenter stage but the kernel reports the sysexit
			   stage; just discard this spurious tracee/event.  */
			if (tracee->exe == NULL) {
				tracee->restart_how = PTRACE_CONT; /* SYSCALL OR CONT */
				return 0;
			}

			switch (tracee->seccomp) {
			case ENABLED:
				if (IS_IN_SYSENTER(tracee)) {
					/* sysenter: ensure the sysexit
					 * stage will be hit under seccomp.  */
					tracee->restart_how = PTRACE_SYSCALL;
					tracee->sysexit_pending = true;
				}
				else {
					/* sysexit: the next sysenter
					 * will be notified by seccomp.  */
					tracee->restart_how = PTRACE_CONT;
					tracee->sysexit_pending = false;
				}
				/* Fall through.  */
			case DISABLED:
				translate_syscall(tracee);

				/* This syscall has disabled seccomp.  */
				if (tracee->seccomp == DISABLING) {
					tracee->restart_how = PTRACE_SYSCALL;
					tracee->seccomp = DISABLED;
				}

				break;

			case DISABLING:
				/* Seccomp was disabled by the
				 * previous syscall, but its sysenter
				 * stage was already handled.  */
				tracee->seccomp = DISABLED;
				if (IS_IN_SYSENTER(tracee))
					tracee->status = 1;
				break;
			}
			break;

		case SIGTRAP | PTRACE_EVENT_SECCOMP2 << 8:
		case SIGTRAP | PTRACE_EVENT_SECCOMP << 8: {
			unsigned long flags = 0;

			signal = 0;

			if (!seccomp_detected) {
				VERBOSE(tracee, 1, "ptrace acceleration (seccomp mode 2) enabled");
				tracee->seccomp = ENABLED;
				seccomp_detected = true;
			}

			/* Use the common ptrace flow if seccomp was
			 * explicitely disabled for this tracee.  */
			if (tracee->seccomp != ENABLED)
				break;

			status = ptrace(PTRACE_GETEVENTMSG, tracee->pid, NULL, &flags);
			if (status < 0)
				break;

			/* Use the common ptrace flow when
			 * sysexit has to be handled.  */
			if ((flags & FILTER_SYSEXIT) != 0) {
				tracee->restart_how = PTRACE_SYSCALL;
				break;
			}

			/* Otherwise, handle the sysenter
			 * stage right now.  */
			tracee->restart_how = PTRACE_CONT;
			translate_syscall(tracee);

			/* This syscall has disabled seccomp, so move
			 * the ptrace flow back to the common path to
			 * ensure its sysexit will be handled.  */
			if (tracee->seccomp == DISABLING)
				tracee->restart_how = PTRACE_SYSCALL;
			break;
		}

		case SIGTRAP | PTRACE_EVENT_VFORK << 8:
			signal = 0;
			(void) new_child(tracee, CLONE_VFORK);
			break;

		case SIGTRAP | PTRACE_EVENT_FORK  << 8:
		case SIGTRAP | PTRACE_EVENT_CLONE << 8:
			signal = 0;
			(void) new_child(tracee, 0);
			break;

		case SIGTRAP | PTRACE_EVENT_VFORK_DONE << 8:
		case SIGTRAP | PTRACE_EVENT_EXEC  << 8:
			signal = 0;
			break;

		case SIGTRAP | PTRACE_EVENT_EXIT  << 8: {
			unsigned long pending_status = 0;
			signal = 0;
			if (ptrace(PTRACE_GETEVENTMSG, tracee->pid, NULL,
					&pending_status) == 0 &&
			    WIFSIGNALED((int) pending_status))
				print_stack_trace(tracee);
			break;
		}

		case SIGSTOP:
			/* Stop this tracee until PRoot has received
			 * the EVENT_*FORK|CLONE notification.  */
			if (tracee->exe == NULL) {
				tracee->sigstop = SIGSTOP_PENDING;
				signal = -1;
			}

			/* For each tracee, the first SIGSTOP
			 * is only used to notify the tracer.  */
			if (tracee->sigstop == SIGSTOP_IGNORED) {
				tracee->sigstop = SIGSTOP_ALLOWED;
				signal = 0;
			}
			break;

		default:
			/* Deliver this signal as-is.  */
			break;
		}
	}

	/* Clear the pending event, if any.  */
	tracee->as_ptracee.event4.proot.pending = false;

	return signal;
}


/**
 * Restart the given @tracee with the specified @signal.  This
 * function returns false if the tracee was not restarted (error or
 * put in the "waiting for ptracee" state), otherwise true.
 */
bool restart_tracee(Tracee *tracee, int signal)
{
	int status;

	/* Put in the "stopped"/"waiting for ptracee" state?.  */
	if (tracee->as_ptracer.wait_pid != 0 || signal == -1)
		return false;

	/* Restart the tracee and stop it at the next instruction, or
	 * at the next entry or exit of a system call. */
	status = ptrace(tracee->restart_how, tracee->pid, NULL, signal);
	if (status < 0)
		return false; /* The process likely died in a syscall.  */

	VERBOSE(tracee, 6, "vpid %" PRIu64 ": restarted using %d, signal %d",
		tracee->vpid, tracee->restart_how, signal);

	tracee->restart_how = 0;
	tracee->running = true;

	return true;
}
