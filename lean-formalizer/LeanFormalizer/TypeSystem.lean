-- Add few instances missing in base lean

abbrev Reader := ReaderM

instance : Applicative List where
  pure x := List.singleton x
  seq mf mx := mf.flatMap λf => mx () |>.flatMap λ x => [f x]

instance : Monad List where
  pure x := List.singleton x
  bind m f := List.flatMap f m

instance : Alternative List where
  failure := []
  orElse xs ys := xs ++ ys ()

instance : Functor (Prod o) where
  map := fun f (o, a) => (o, f a)

def Cont (r : Type) (a : Type) := (a -> r) -> r

instance : Functor (Cont r) where
  map f m := fun k => m (fun a => k (f a))

instance : Applicative (Cont r) where
  pure x := fun k => k x
  seq mf mx := fun k => mf (fun f => mx () (fun x => k (f x)))

instance : Monad (Cont r) where
  pure x := fun k => k x
  bind x f g := x fun i => f i g


class Adjoint (f g : Type -> Type) [Functor f] [Functor g] where
  unit   : a -> g (f a)
  counit : f (g a) -> a
  phi  : (f a -> b) -> a -> g b := fun c => Functor.map c ∘ unit
  psi  : (a -> g b) -> f a -> b := fun k => counit ∘ Functor.map k

instance : Adjoint (Prod e) (Reader e) where
  unit x := λ io => (io, x)
  counit p := p.2 p.1

-- Define Type System

mutual
inductive FX where
  | maybe
  | set
  | read (iota : Ty)
  | write (omicron : Ty)
  | cont (rho : Ty)
deriving BEq, DecidableEq

inductive Ty where
  | elem
  | truth
  | fn (a r: Ty)
  | comp (f : FX) (a : Ty)
deriving BEq, DecidableEq
end

@[match_pattern] abbrev E := Ty.elem
@[match_pattern] abbrev T := Ty.truth
@[match_pattern] abbrev S a := Ty.comp FX.set a
@[match_pattern] abbrev M a := Ty.comp FX.maybe a
syntax "R^" term:max term:max : term
syntax "W^" term:max term:max : term
syntax "C^" term:max term:max : term
macro_rules
  | `(R^$e $a) => `(Ty.comp (FX.read $e) $a)
  | `(W^$o $a) => `(Ty.comp (FX.write $o) $a)
  | `(C^$r $a) => `(Ty.comp (FX.cont $r) $a)
infixr:50 " ~> " => Ty.fn


mutual 
@[reducible]
def FX.dom : FX → Type → Type
  | .set => List
  | .maybe => Option 
  | .write o => Prod o.dom
  | .read i => Reader i.dom
  | .cont r => Cont r.dom

@[reducible]
def Ty.dom : Ty → Type
  | .elem => Nat
  | .truth => Bool
  | .fn a r => a.dom -> r.dom
  | .comp f a => f.dom a.dom
end


def functor : (f : FX) -> Option (Functor f.dom)
  | .set | .maybe | .write _ | .read _ | .cont _ => some (inferInstanceAs _)

def applicative : (f : FX) -> Option (Functor f.dom)
  | .set | .maybe | .read _ | .cont _ => some (inferInstanceAs _)
  | _ => none

def monad : (f : FX) -> Option (Monad f.dom)
  | .set | .maybe | .read _ | .cont _ => some (inferInstanceAs _)
  | _ => none

def adjoint : (f g : FX) -> Option ((_ : Functor f.dom) × (_ : Functor g.dom) × Adjoint f.dom g.dom)
  | .write o, .read e =>
      if h : o = e then by subst h; exact some ⟨_, _, inferInstanceAs _⟩
      else none
  | _, _ => none

def Ty.commutative (t : Ty) : Bool := t == T

def FX.commutative : (f : FX) -> Bool
  | .set | .read _ => true
  | .write o => Ty.commutative o
  | _ => false

inductive Cat : Type where
  | CP | Cmp
  | CBar | DBar | Cor -- Coordinators and Coordination Phrases
  | DP | Det | Gen | GenD | Dmp -- (Genitive) Determiners and full Determiner Phrases
  | NP | TN -- Transitive (relational) Nouns and full Noun Phrases
  | VP | TV | DV | AV -- Transitive, Ditransitive, and Attitude Verbs and Verb Phrases
  | AdjP | TAdj | Deg | AdvP | TAdv -- Modifiers
deriving Repr

abbrev CFG := Cat -> Cat -> List Cat

inductive Tree (c: Type) (a: Type): Type where
  | leaf : c -> a -> Tree c a
  | node : c -> Tree c a -> Tree c a -> Tree c a
deriving Repr

def Tree.root : (t : Tree c a) -> c
  | .leaf c _ => c
  | .node c _ _ => c


inductive ModeLabel : Type where
  | FA | BA | PM
  | MR (m : ModeLabel) | ML (m : ModeLabel)
  | AP (m : ModeLabel)
  | UR (m : ModeLabel) | UL (m : ModeLabel)
  | CU (m : ModeLabel)
  | JN (m : ModeLabel)
  | DN (m : ModeLabel)
deriving BEq, DecidableEq


section
open ModeLabel Lean
def ModeLabel.build : List Syntax -> MacroM (TSyntax `term)
  | [] => Macro.throwError "Empty mode label sequence"
  | [m] => `($(mkIdent m.getId))
  | m :: ms => build ms >>= fun inner => `($(Lean.mkIdent m.getId) $inner)

syntax "m:" ident+ : term
macro_rules
  | `(m: $ids*) => build ids.toList

#eval match MR (AP FA) with
  | m:MR ML __ => true
  | m:MR MR __ => false
  | _ => true
end

structure Mode (α : Type) (β : Type) (γ : Type) where
  mode : ModeLabel
  op : α → β → γ

inductive Expr : Ty -> Type where
  | lex: String -> a.dom -> Expr a
  | moc : Mode a.dom b.dom c.dom -> Expr a -> Expr b -> Expr c

def Expr.den : Expr ty → ty.dom
  | lex _ x => x 
  | moc ⟨_, o⟩  x y => o (x.den) (y.den) 

def exprTest (x y : Nat) : Expr T :=
  .moc ⟨.BA, flip id⟩ sub (.moc ⟨.FA, id⟩ exc obj)
  where sub : Expr E := .lex "sub" x
        obj : Expr E := .lex "obj" y
        exc : Expr (E~>E~>T) := .lex "exceeds" (·<·)

def TypedExpr := (t : Ty) × Expr t
def Exprs := List ((t : Ty) × Expr t)
def Interps (t : Ty) := List (Expr t × t.dom)

section
open ModeLabel
variable {α α' β β' γ : Type}

def Mode.fa : Mode (α → β) α β := ⟨FA, (·<|·)⟩ 
def Mode.ba : Mode α (α → β) β := ⟨BA, (·|>·)⟩
def Mode.pm : Mode (α → Bool) (α → Bool) (α → Bool) := ⟨PM, fun p q x => p x && q x⟩

variable {f g : Type -> Type}
def Mode.ml [Functor f] (m : Mode α β γ) : Mode (f α) β (f γ) :=
  ⟨ML m.mode, fun xs y  => xs <&> (fun a => m.op a y)⟩

def Mode.mr [Functor f] (m : Mode α β γ) : Mode α (f β) (f γ) :=
  ⟨MR m.mode, fun x ys  => (fun b => m.op x b) <$> ys⟩

def Mode.ap [Applicative f] (m : Mode α β γ) : Mode (f α) (f β) (f γ) :=
  ⟨AP m.mode, fun xs ys => m.op <$> xs <*> ys⟩

def Mode.ul [Applicative f] (m : Mode α (β → β') γ) : Mode α (f β → β') γ :=
  ⟨UL m.mode, fun x y => m.op x (fun b => y (pure b))⟩

def Mode.ur [Applicative f] (m : Mode (α → α') β γ) : Mode (f α → α') β γ :=
  ⟨UL m.mode, fun x y => m.op (fun a => x (pure a)) y⟩

def Mode.cu [Functor f] [Functor g] [Adjoint f g] (m : Mode α β γ) : Mode (f α) (g β) γ :=
  ⟨CU m.mode, fun xs ys => Adjoint.counit ((fun a => m.op a <$> ys) <$> xs)⟩

def Mode.jn [Monad f] (m : Mode α β (f (f γ))) : Mode α β (f γ) :=
  ⟨JN m.mode, fun x y => m.op x y >>= id⟩

def Mode.dn (m : Mode α β (Cont γ γ)) : Mode α β γ :=
  ⟨DN m.mode, fun x y => m.op x y id⟩

end
