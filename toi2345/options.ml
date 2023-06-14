let debug_flag = Sys.getenv_opt "DEBUG" = Some "true"
let inference_only = Sys.getenv_opt "INFER_ONLY" = Some "true"

let compress_type = Sys.getenv_opt "COMPRESS_TYPE" = Some "true"