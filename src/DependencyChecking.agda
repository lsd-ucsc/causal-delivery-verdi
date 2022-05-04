open import Data.Nat as ℕ

module DependencyChecking (n : ℕ) (RawMsg : Set) where

open import Function hiding (id)
open import Data.Maybe
open import Data.Bool
open import Data.Fin as Fin
open import Data.Product
open import Data.List as List hiding (null)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.Unit
open import Relation.Nullary using (Dec; yes; no)

open import Verdi

Node = Fin n

record MsgId : Set where
  field
    pid : Node
    ct  : ℕ

Deps : Set
Deps = List MsgId

record Msg : Set where
  field
    id  : MsgId
    deps : Deps
    raw : RawMsg

data Input : Set where
  send : (dst : Node) → (raw : RawMsg) → Input
  deliver : Input

data Output : Set where
  deliver : RawMsg → Output
  null    : Output

record Process : Set where
  field
    id : Node
    deps : Deps
    msgCt : ℕ
    dq : List Msg

-- deliverable : (p : Process) → (m : Msg) → Dec (Msg.deps m ⊆ Process.deps p)
_==_ : MsgId → MsgId → Bool
deliverable : Process → Msg → Bool
deliverable p m = all (λ d → any (d ==_ ) (Process.deps p)) (Msg.deps m)

handleInput : Node → Process → Input → Process × Output × List (Packet Node Msg)
handleInput src p (send dst raw) = p′ , deliver raw ,  [ src ⇒ dst ⦂ msg ]
  where
    msgid = record { pid = Process.id p ; ct = Process.msgCt p }
    msg = record { id = msgid ; deps = Process.deps p ; raw = raw }
    p′ = record p { deps = msgid ∷ (Process.deps p) ; msgCt = (Process.msgCt p) ℕ.+ 1}
handleInput src p deliver = case processDq (Process.dq p) of λ
  { (dq′ , just  record { id = id ; raw = raw ; deps = deps }) → record p { deps = id ∷ deps ++ Process.deps p } , deliver raw , []
  ; (_   , nothing)                                            → p , null , []
  }
  where
    processDq : List Msg → List Msg × Maybe Msg
    processDq []       = [] , nothing
    processDq (x ∷ xs) = case deliverable p x of λ where
      true  → xs , just x
      false → let xs′ , m = processDq xs
              in x ∷ xs , m

handleMsg : Node → Process → Packet Node Msg → Process × Output × List (Packet Node Msg)
handleMsg dst p (_ ⇒ _ ⦂ msg) = p″ , null , []
  where
    p″ = record p { dq = msg ∷ Process.dq p }

DependencyChecking : App
DependencyChecking = record
                { Node = Node
                ; _≟_ = Fin._≟_
                ; State = λ _ → Process
                ; Msg = Msg
                ; Input = Input
                ; Output = Output
                ; initState = λ id → record { id = id ; deps = [] ; msgCt = 0 ; dq = [] }
                ; HandleInp = handleInput
                ; HandleMsg = handleMsg
                }
