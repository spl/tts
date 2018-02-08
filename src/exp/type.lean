namespace tts ------------------------------------------------------------------

-- Grammar of expressions.
inductive exp (V : Type) : Type
  | varb {} : ℕ → exp          -- bound variable
  | varf    : V → exp          -- free variable
  | app     : exp → exp → exp  -- function application
  | lam     : exp → exp        -- lambda-abstraction
  | let_    : exp → exp → exp  -- let-abstraction

end /- namespace -/ tts --------------------------------------------------------
