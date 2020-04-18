from std/strutils import split, join, indent
from macros import nil

func strip_ends(str: string): string =
   let lines = str.split('\n')
   var new_lines = seq[string].default
   for i, line in lines:
      if line.len == 0 and (i == lines.low or i == lines.high): continue
      new_lines.add(line)
   result = new_lines.join("\n")

func enclose*(str: string): string =
   result = str.strip_ends
   if result.split("\n").len > 1:
      result = "'''\n" & result.indent(2) & "\n'''"
   else:
      result = '\'' & result & '\''

proc expect_string*[T](cond: string, info: string, val: T): string =
   result = "\nExpectation failed: '" & cond & "'\n"
   if info.len > 0:
      result &= "Info: " & info & "\n"
   mixin verbose_note
   result &= verbose_note(val)
   result = result.indent(2)

template impl_expect*(cond, msg, val) =
   {.line.}:
      if not(cond):
         macros.error(expect_string(ast_to_str(cond), msg, val), when val is NimNode: val
                                                                 else: val.detail)
