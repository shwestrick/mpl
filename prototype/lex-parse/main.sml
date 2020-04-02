val fileNames = CommandLine.arguments ()

fun doFile name =
  ( print ("PROCESSING FILE: " ^ name ^ "\n")
  ; LexParse.lexAndParseFile name
  ; ()
  )

val _ = List.app doFile fileNames
