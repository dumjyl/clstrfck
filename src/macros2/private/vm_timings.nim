when defined(vm_timings):
   import
      std/tables,
      std/times,
      std/os,
      std/algorithm,
      private/macros_core

   var timings {.compile_time.} = init_Table[string, seq[float]]()

   const expr_kinds = nnk_call_kinds + {nnk_obj_constr, nnk_dot_expr}

   macro time*(fn): untyped =
      result = fn
      let name = lit(fn.line_info_obj.file_name.split_file.name & "(" & $fn.line_info_obj.line &
                     ")@" & $fn.name)
      if fn.params[0].kind != nnk_empty and fn.body.len == 1 and fn.body[0] of expr_kinds:
         fn.body[0] = !(result = `fn.body[0]`)
      let time_sym = nsk_let.gen
      let duration_sym = nsk_let.gen
      fn.body.insert(0, AST do:
         {.no_side_effect.}:
            let `time_sym` = `bind cpu_time`())
      fn.body.add(AST do:
         defer:
            {.no_side_effect.}:
               let `duration_sym` = `bind cpu_time`() - `time_sym`
               `bind timings`.`bind mget_or_put`(`name`, @[]).add(`duration_sym`))

   func sum(durations: seq[float]): float =
      var sum = 0f64
      for duration in durations:
         sum += duration
      result = sum

   proc log_timings* =
      var info = seq[(float, string)].default
      for name, durations in timings:
         info.add (durations.sum,
                   name & "; " & $durations.sum & " sec total; " & $durations.len & " hits")
      info.sort
      for (_, str) in info:
         echo str
else:
   macro time*(fn: untyped): untyped = fn
