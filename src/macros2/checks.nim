import ../macros2; export macros2
import ../options2; export options2

func contains*(names: openarray[string], ident: Ident): bool =
   for name in names:
      if ident == name:
         return true

template impl_is_call(fn_name, T) {.dirty.} =
   proc fn_name*(self: Stmt, name: string, len: int): Option[T] =
      ## Does not consider a symbol a match for name, only idents.
      match self of T and self.name as self_name of Ident and self_name == name and
            self.args.len == len:
        result = some(self)

   proc fn_name*(self: Stmt, names: openarray[string], len: int): Option[T] =
      ## Does not consider a symbol a match for name, only idents.
      match self of T and self.name of Ident and name in names and self.args.len == len:
        result = some(self)


impl_is_call(is_command_call, CommandCall)
impl_is_call(is_call, Call)
