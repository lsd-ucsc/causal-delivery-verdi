open import Data.Nat as ℕ

module DependencyTracking (n : ℕ) (RawMsg : Set) where

open import Data.Fin as Fin
open import Data.Product
open import Data.List
open import Data.Unit

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

data Output : Set where
  deliver : RawMsg → Output

record Process : Set where
  field
    id : Node
    deps : Deps
    msgCt : ℕ

handleInput : Node → Process → Input → Process × Output × List (Packet Node Msg)
handleInput src p (send dst raw) = p′ , deliver raw ,  [ src ⇒ dst ⦂ msg ]
  where
    msgid = record { pid = Process.id p ; ct = Process.msgCt p }
    msg = record { id = msgid ; deps = Process.deps p ; raw = raw }
    p′ = record p { deps = msgid ∷ (Process.deps p) ; msgCt = (Process.msgCt p) ℕ.+ 1}

handleMsg : Node → Process → Packet Node Msg → Process × Output × List (Packet Node Msg)
handleMsg dst p (_ ⇒ _ ⦂ record { raw = raw ; deps = deps }) = p′ , deliver raw , []
  where
    p′ = record p { deps = deps ++ Process.deps p }

DependencyTracking : App
DependencyTracking = record
                { Node = Node
                ; _≟_ = Fin._≟_
                ; State = λ _ → Process
                ; Msg = Msg
                ; Input = Input
                ; Output = Output
                ; initState = λ id → record { id = id ; deps = [] ; msgCt = 0 }
                ; HandleInp = handleInput
                ; HandleMsg = handleMsg
                }
