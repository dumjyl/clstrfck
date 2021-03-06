import
   pkg/when_native,
   pkg/macros2/private/core,
   std/os

# handling vm
# FIXME: map fatal -> macros.error
# FIXME: map main -> to a mostly nop for
# loses destructors but probably fine.

type
   Logger* {.pure, inheritable.} = object ## base Logger, for no real purpose yet.
   Out* = object of Logger ## Output to `stdout`
   Err* = object of Logger ## Output to `stderr`

template get_buffer: string = new_string_of_cap(512)

template file*(Self: type[Out] | Out): File = stdout
   ## Return the `File` that `Self` is assoicated with.

template file*(Self: type[Err] | Err): File = stderr
   ## Return the `File` that `Self` is assoicated with.

macro log*(Self: type[Logger], arguments: varargs[untyped]) =
   let buf = nskVar.gen("buf")
   let stmts = nnkStmtList{}
   for argument in arguments:
      stmts.add(!`buf`.add(`argument`))
   result = AST:
      block:
         when_native:
            let file = `Self`.file
            # FIXME: nim bug: this gets c compiler error without decl.
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
   when_native: (is_clicolor_env() and is_a_tty(stdout)) or is_clicolor_force_env()
   else: is_clicolor_env() or is_clicolor_force_env()

proc is_clicolor(f: File): bool =
   result = (is_clicolor_env() and is_a_tty(f)) or is_clicolor_force_env()

proc is_no_color: bool = exists_env("NO_COLOR")

proc is_color_enabled(f: File): bool = not is_no_color() and is_clicolor(f)

proc is_color_enabled: bool = not is_no_color() and is_clicolor()

proc cmd(code: int): string = "\e[" & $code & 'm'

proc apply(str: string, code: int, enabled: bool = is_color_enabled()): string =
   if enabled: cmd(code) & str & cmd(0) else: str

macro impl =
   result = nnkStmtList{}
   for code, color in [30: "black", "red", "green", "yellow", "blue",
                       35: "magenta", "cyan", "white"]:
      let code = code.lit
      for (name, ast) in {pub_ident(color): !`code`,
                          pub_ident("bg_" & color): !(`code` + 10),
                          pub_ident("bright_" & color): !(`code` + 60),
                          pub_ident("bg_bright_" & color): !(`code` + 10 + 60)}:
         let is_color_enabled = "is_color_enabled".bind_ident
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

# FIXME: Remap exceptions to same style.

type ExitRequest* = object of CatchableError
   exit_code*: int
   write_trace*: bool

proc init(msg: string, exit_code: int, write_trace: bool): ref ExitRequest =
   result = (ref ExitRequest)(msg: msg, exit_code: exit_code, write_trace: write_trace)

macro exit*(write_trace = false) =
   result = AST: raise `bind init`("", 0, `write_trace`)

macro exit*(msg: string, write_trace = false) =
   result = AST: raise `bind init`(`msg`, 0, `write_trace`)

macro exit*(exit_code: int, write_trace = false) =
   result = AST: raise `bind init`("", `exit_code`, `write_trace`)

macro exit*(msg: string, exit_code: int, write_trace = false) =
   result = AST: raise `bind init`(`msg`, `exit_code`, `write_trace`)

proc add*(self: var string, entry: StackTraceEntry) =
   self.add(entry.filename)
   self.add('(')
   self.add_int(entry.line)
   self.add(") ")
   self.add(entry.proc_name)

proc write_trace(exit_request: ref ExitRequest) =
   # FIXME: non native supprt :-/
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
   when_native:
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
