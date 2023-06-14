module SchemaEnv = Schema.SchemaEnv

exception BadConstraintError of Type.t * Type.t

exception RecursiveOccurenceError of Type.typevar_t * Type.t

val infer_command :
  SchemaEnv.t -> Expr.t Command.command -> Schema.schema list * SchemaEnv.t
