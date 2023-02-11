/* SPDX-License-Identifier: GPL-2.0 */
#undef TRACE_SYSTEM
#define TRACE_SYSTEM rust 

#if !defined(_TRACE_RUST_H) || defined(TRACE_HEADER_MULTI_READ)
#define _TRACE_RUST_H

#include <linux/tracepoint.h>

TRACE_EVENT(arc_drop_inner,
	TP_PROTO(const char *name, unsigned long name_len, const void* ptr),

	TP_ARGS(name, name_len, ptr),

	TP_STRUCT__entry(
		__field(const char *, name)
		__field(unsigned long, name_len)
		__field(const void *, ptr)
	),

	TP_fast_assign(
		__entry->name = name;
		__entry->name_len = name_len;
		__entry->ptr = ptr;
	),

	TP_printk("Arc<%*.s> (%p) drop inner",
		__entry->name_len, __entry->name, __entry->ptr)
);

#endif /*  _TRACE_RUST_H */

/* This part must be outside protection */
#include <trace/define_trace.h>
