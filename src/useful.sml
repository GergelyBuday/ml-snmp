structure Useful =
struct
 fun onespace str =
  let
   fun  list_onespace []          puffer        = puffer
   |    list_onespace (#" " :: chs)  puffer     = in_space chs puffer
   |    list_onespace (#"\t" :: chs) puffer     = in_space chs puffer
   |    list_onespace (#"\n" :: chs) puffer     = in_space chs puffer
   |    list_onespace (ch::chs)   puffer        = list_onespace chs (ch::puffer)   and  in_space []             puffer  = puffer
   |    in_space (#" " :: chs)  puffer  = in_space chs puffer
   |    in_space (#"\t" :: chs) puffer  = in_space chs puffer
   |    in_space (#"\n" :: chs) puffer  = in_space chs puffer
   |    in_space (ch::chs)      puffer  = list_onespace chs (ch:: #" " ::puffer)  in
   implode (rev (list_onespace (explode str) []) )
  end

 fun numberofnl str =
        let
         fun nl [] = 0
           | nl (#"\n" :: chs) = 1 + nl chs
           | nl (_ :: chs) = nl chs
        in
         nl (explode str)
        end
 fun error (e,l : int) = TextIO.output (TextIO.stdErr, String.concat[
        "line ", (Int.toString l), ": ", e, "\n"
      ])

end
