## Provides output and error output routines for the native backend and the vm/nimscript.
## Also provides context and environment aware coloring routines.
##
## Respects https://bixense.com/clicolors/ and https://no-color.org/

## This module trys to provide reliable and pretty application cleanup/termination handling.

import
   pkg/clstrfck/private/macros_core,
   std/os

macro when_native*(branches: varargs[untyped]): untyped {.AST.} =
   escape:
      branches.expect(1 .. 2)
      for branch in branches:
         branch.expect({nnk_stmt_list, nnk_else})
      var non_native = if branches.len == 2: branches[1][0]
                       else: nnk_discard_stmt.init(empty)
   when nim_vm:
      `non_native`
   else:
      when defined(nim_script) or defined(js):
         `non_native`
      else:
         `branches[0]`

type
   Logger* {.pure, inheritable.} = object ## base Logger, for no real purpose yet.
   Out* = object of Logger ## Output to `stdout`
   Err* = object of Logger ## Output to `stderr`

template get_buffer: string = new_string_of_cap(512)

template file*(Self: type[Out] | Out): File = stdout
   ## Return the `File` that `Self` is assoicated with.

template file*(Self: type[Err] | Err): File = stderr
   ## Return the `File` that `Self` is assoicated with.

macro log*(Self: type[Logger], arguments: varargs[untyped]) {.AST.} =
   escape:
      let buf = nsk_var.init("buf")
      let stmts = gen_stmts()
      for argument in arguments:
         stmts.add(!`buf`.add(`argument`))
   block:
      when_native:
         let file = `Self`.file
         # XXX: nim bug: this gets c compiler error without decl.
         var `buf` = get_buffer()
         `stmts`
         `buf`.add('\n')
         file.write(`buf`)
         file.flush_file
      else:
         var `buf` = get_buffer()
         `stmts`
         echo `buf`

proc is_a_tty(f: File): bool =
   when defined(posix):
      proc is_a_tty(file_handle: FileHandle): c_int
         {.import_c: "isatty", header: "<unistd.h>".}
   else:
      proc is_a_tty(file_handle: FileHandle): c_int
         {.import_c: "_isatty", header: "<io.h>".}
   result = is_a_tty(get_file_handle(f)) != 0'i32

proc is_clicolor_env: bool = get_env("CLICOLOR", "1") != "0"

proc is_clicolor_force_env: bool = get_env("CLICOLOR_FORCE", "0") != "0"

proc is_clicolor: bool =
   template tmpl: auto = is_clicolor_env() or is_clicolor_force_env()
   when nim_vm: tmpl()
   else:
      when defined(nim_script) or defined(js): tmpl()
      else: (is_clicolor_env() and is_a_tty(stdout)) or is_clicolor_force_env()

proc is_clicolor(f: File): bool =
   result = (is_clicolor_env() and is_a_tty(f)) or is_clicolor_force_env()

proc is_no_color: bool = exists_env("NO_COLOR")

proc is_color_enabled(f: File): bool = not is_no_color() and is_clicolor(f)

proc is_color_enabled: bool = not is_no_color() and is_clicolor()

proc cmd(code: int): string = "\e[" & $code & 'm'

proc apply(str: string, code: int, enabled: bool = is_color_enabled()): string =
   if enabled: cmd(code) & str & cmd(0) else: str

macro impl =
   result = gen_stmts()
   for code, color in [30: "black", "red", "green", "yellow", "blue",
                       35: "magenta", "cyan", "white"]:
      let code = code.new_lit
      for (name, ast) in {pub_ident(color): !`code`,
                          pub_ident("bg_" & color): !(`code` + 10),
                          pub_ident("bright_" & color): !(`code` + 60),
                          pub_ident("bg_bright_" & color): !(`code` + 10 + 60)}:
         let is_color_enabled = "is_color_enabled".bind_sym
         let call = name[1]
         result.add_AST:
            template `name`(str: string, enabled: bool): string =
               `bind apply`(str, `ast`, enabled)
            template `name`(str: string, f: File): string =
               `call`(str, `is_color_enabled`(f))
            template `name`(Self: type[Logger], str: string): string =
               when_native:
                  `call`(str, `is_color_enabled`(Self.`bind file`))
               else:
                  `call`(str, `is_color_enabled`())
            template `name`(str: string): string =
               when_native:
                  `call`(str, stdout)
               else:
                  `call`(str, `is_color_enabled`())
impl()

# TODO: Remap exceptions to same style.

type ExitRequest* = object of CatchableError
   exit_code*: int
   write_trace*: bool

proc init(
      msg: string,
      exit_code: int,
      write_trace: bool
      ): ref ExitRequest =
   result = (ref ExitRequest)(msg: msg, exit_code: exit_code,
                              write_trace: write_trace)

template exit*(write_trace = false) =
   raise mainframe.init("", 0, write_trace)

template exit*(msg: string, write_trace = false) =
   raise mainframe.init(msg, 0, write_trace)

template exit*(exit_code: int, write_trace = false) =
   raise mainframe.init("", exit_code, write_trace)

template exit*(msg: string, exit_code: int, write_trace = false) =
   raise mainframe.init(msg, exit_code, write_trace)

proc add*(self: var string, entry: StackTraceEntry) =
   self.add(entry.filename)
   self.add('(')
   self.add_int(entry.line)
   self.add(") ")
   self.add(entry.proc_name)

proc write_trace(exit_request: ref ExitRequest) =
   # TODO: non native supprt :-/
   let entries = exit_request.get_stack_trace_entries()
   if exit_request.write_trace and entries.len > 0:
      var buf: string
      buf.add(Err.bright_yellow("Traceback:"))
      if entries.len == 1:
         buf.add(' ')
         buf.add(entries[0])
      else:
         buf.add('\n')
         for i, entry in entries:
            buf.add(entry)
            if i != entries.high:
               buf.add('\n')
      Err.log(buf)

proc finish*(exit_request: ref ExitRequest) {.no_return.} =
   write_trace(exit_request)
   if exit_request.msg.len == 0:
      quit(exit_request.exit_code)
   else:
      quit(exit_request.msg, exit_request.exit_code)

template exit_handler*(stmts: untyped) =
   try:
      stmts
   except ExitRequest as exit_request:
      finish(exit_request)

template exit_handler*(on_exit: untyped, stmts: untyped) =
   when nimvm: discard
   else:
      when not defined(nim_script):
         set_control_c_hook(proc {.no_conv.} =
            write(stderr, stderr.bright_yellow("Signal Interrupt:"), " ctrl-c")
            on_exit
            quit(1))
   try:
      stmts
   except ExitRequest as exit_request:
      on_exit
      finish(exit_request)

template main*(stmts: untyped) =
   when is_main_module:
      proc main_fn: int {.gen_sym.} =
         exit_handler(stmts)
      {.line.}: quit(main_fn())

template main*(on_exit: untyped, stmts: untyped) =
   when is_main_module:
      proc main_fn: int {.gen_sym.} =
         exit_handler(on_exit, stmts)
         on_exit
      {.line.}: quit(main_fn())

template fatal*(msgs: varargs[string, `$`]) =
   var buf = get_buffer()
   buf.add(Err.bright_red("Error:"))
   buf.add(' ')
   for msg in msgs:
      buf.add(msg)
   {.line.}: exit(buf, 1, true)
