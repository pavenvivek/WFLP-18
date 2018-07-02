{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-auto-inline #-}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --verbose tc.sample.debug:20 #-}

open import Function renaming (_∘_ to _○_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Reflection
open import Data.List
open import Patch_Theory.agda_lib.Utils

open import Patch_Theory.cryptography.Paillier-Cryptosystem
open import Patch_Theory.cryptography.RSA-Cryptosystem
open import Patch_Theory.cryptography.OPE-Cryptosystem
open import Patch_Theory.cryptography.ElGamal-Cryptosystem
open import Patch_Theory.cryptography.insert-delete-query
open import Patch_Theory.cryptography.increment-path
open import Patch_Theory.cryptography.encrypted-increment

open import Automation.lib.generateRec
open import Automation.lib.generateInd
open import Automation.lib.generateHit
open import Automation.lib.generateRecHit
open import Automation.lib.generateIndHit
open import Automation.utils.reflectionUtils
open import Automation.utils.pathUtils
open import Automation.lib.generateBetaRecHit
open import Automation.lib.generateBetaRecHitPath using (generateβRecHitPath)
open import Automation.lib.generateBetaRec
open import Automation.lib.generateBetaIndHit
open import Automation.lib.generateBetaIndHitPath using (generateβIndHitPath)
open import Automation.lib.generateBetaInd


module Patch_Theory.cryptography.repository where

module History_hit where

{-- Records : Higher inductive type which stores the instances of all the queries executed --}

  postulate
      History : Nat → Nat → Set
      []R : {m : Nat} → History m m
      ID-R:: : {m n : Nat} → History m n → History m n
      INSERT_at_::_ : {m n : Nat} → (value : Nat) → (i : Nat) → History m n → History m (suc n)
      DELETE_::_ : {m n : Nat} → (i : Nat) → History m (suc n) → History m n
      RSA-ENCRYPT_,_::_ : {m n : Nat} → (p : Nat) → (q : Nat) → History m n → History m n
      RSA-DECRYPT_,_::_ : {m n : Nat} → (p : Nat) → (q : Nat) → History m n → History m n
      PAILLIER-ENCRYPT_,_::_ : {m n : Nat} → (p : Nat) → (q : Nat) → History m n → History m n
      PAILLIER-DECRYPT_,_::_ : {m n : Nat} → (p : Nat) → (q : Nat) → History m n → History m n
      OPE-ENCRYPT::_ : {m n : Nat} → History m n → History m n
      OPE-DECRYPT::_ : {m n : Nat} → History m n → History m n
      ELGAMAL-ENCRYPT_::_ : {m n : Nat} → (p : Nat) → History m n → History m n
      ELGAMAL-DECRYPT_::_ : {m n : Nat} → (p : Nat) → History m n → History m n
      INCREMENT100_::_ : {m n : Nat} → (i : Nat) → History m n → History m n
      CRYPT-INCREMENT100_,_,_::_ : {m n : Nat} → (p q : Nat) → (i : Nat) → History m n → History m n
      PAILLIER-HOMOMORPHISM_,_,_::_ : {m n : Nat} → (p q : Nat) → (i : Nat) → (r : History m n) →
                                      (PAILLIER-DECRYPT_,_::_ {m} {n} p q (CRYPT-INCREMENT100_,_,_::_ {m} {n} p q i
                                      (PAILLIER-ENCRYPT_,_::_ {m} {n} p q r))) ≡ (INCREMENT100_::_  {m} {n} i r)

  Recpoints : List Name
  Recpoints = ((quote []R) ∷ (quote ID-R::) ∷ (quote INSERT_at_::_) ∷ (quote DELETE_::_) ∷ (quote RSA-ENCRYPT_,_::_) ∷ (quote RSA-DECRYPT_,_::_) ∷
               (quote PAILLIER-ENCRYPT_,_::_) ∷ (quote PAILLIER-DECRYPT_,_::_) ∷ (quote OPE-ENCRYPT::_) ∷ (quote OPE-DECRYPT::_) ∷ (quote ELGAMAL-ENCRYPT_::_) ∷
               (quote ELGAMAL-DECRYPT_::_) ∷ (quote INCREMENT100_::_) ∷ (quote CRYPT-INCREMENT100_,_,_::_) ∷ [])

  Recpaths : List Name
  Recpaths = (quote PAILLIER-HOMOMORPHISM_,_,_::_) ∷ []

  unquoteDecl recHistory* β[]R* βID-R::* βINSERT_at_::_* βDELETE_::_* βRSA-ENCRYPT_,_::_* βRSA-DECRYPT_,_::_* βPAILLIER-ENCRYPT_,_::_* βPAILLIER-DECRYPT_,_::_*
                                βOPE-ENCRYPT::_* βOPE-DECRYPT::_* βELGAMAL-ENCRYPT_::_* βELGAMAL-DECRYPT_::_* βINCREMENT100_::_* βCRYPT-INCREMENT100_,_,_::_*
                                = generateβRec (vArg recHistory*)
                                     ((vArg β[]R*) ∷ (vArg βID-R::*) ∷ (vArg βINSERT_at_::_*) ∷ (vArg βDELETE_::_*) ∷ (vArg βRSA-ENCRYPT_,_::_*) ∷ (vArg βRSA-DECRYPT_,_::_*) ∷
                                      (vArg βPAILLIER-ENCRYPT_,_::_*) ∷ (vArg βPAILLIER-DECRYPT_,_::_*) ∷ (vArg βOPE-ENCRYPT::_*) ∷ (vArg βOPE-DECRYPT::_*) ∷ (vArg βELGAMAL-ENCRYPT_::_*) ∷
                                      (vArg βELGAMAL-DECRYPT_::_*) ∷ (vArg βINCREMENT100_::_*) ∷ (vArg βCRYPT-INCREMENT100_,_,_::_*) ∷ [])
                                     (quote History) 0 Recpoints

  {-# REWRITE β[]R* #-}
  {-# REWRITE βID-R::* #-}
  {-# REWRITE βINSERT_at_::_* #-}
  {-# REWRITE βDELETE_::_* #-}
  {-# REWRITE βRSA-ENCRYPT_,_::_* #-}
  {-# REWRITE βRSA-DECRYPT_,_::_* #-}
  {-# REWRITE βPAILLIER-ENCRYPT_,_::_* #-}
  {-# REWRITE βPAILLIER-DECRYPT_,_::_* #-}
  {-# REWRITE βOPE-ENCRYPT::_* #-}
  {-# REWRITE βOPE-DECRYPT::_* #-}
  {-# REWRITE βELGAMAL-ENCRYPT_::_* #-}
  {-# REWRITE βELGAMAL-DECRYPT_::_* #-}
  {-# REWRITE βINCREMENT100_::_* #-}
  {-# REWRITE βCRYPT-INCREMENT100_,_,_::_* #-}


  unquoteDecl recHistory = generateRecHit (vArg recHistory)
                                     (quote History)
                                     (quote recHistory*) 0 Recpoints Recpaths



  unquoteDecl βrecHistory-paiHom = generateβRecHitPath (quote recHistory)
                                     ((vArg βrecHistory-paiHom) ∷ [])
                                     (quote History)
                                     (quote recHistory*) 0 Recpoints Recpaths

-- -------

  unquoteDecl indHistory* iβ[]R* iβID-R::* iβINSERT_at_::_* iβDELETE_::_* iβRSA-ENCRYPT_,_::_* iβRSA-DECRYPT_,_::_* iβPAILLIER-ENCRYPT_,_::_* iβPAILLIER-DECRYPT_,_::_*
                                iβOPE-ENCRYPT::_* iβOPE-DECRYPT::_* iβELGAMAL-ENCRYPT_::_* iβELGAMAL-DECRYPT_::_* iβINCREMENT100_::_* iβCRYPT-INCREMENT100_,_,_::_*
                                = generateβInd (vArg indHistory*)
                                     ((vArg iβ[]R*) ∷ (vArg iβID-R::*) ∷ (vArg iβINSERT_at_::_*) ∷ (vArg iβDELETE_::_*) ∷ (vArg iβRSA-ENCRYPT_,_::_*) ∷ (vArg iβRSA-DECRYPT_,_::_*) ∷
                                      (vArg iβPAILLIER-ENCRYPT_,_::_*) ∷ (vArg iβPAILLIER-DECRYPT_,_::_*) ∷ (vArg iβOPE-ENCRYPT::_*) ∷ (vArg iβOPE-DECRYPT::_*) ∷ (vArg iβELGAMAL-ENCRYPT_::_*) ∷
                                      (vArg iβELGAMAL-DECRYPT_::_*) ∷ (vArg iβINCREMENT100_::_*) ∷ (vArg iβCRYPT-INCREMENT100_,_,_::_*) ∷ [])
                                     (quote History) 0 Recpoints

  {-# REWRITE iβ[]R* #-}
  {-# REWRITE iβID-R::* #-}
  {-# REWRITE iβINSERT_at_::_* #-}
  {-# REWRITE iβDELETE_::_* #-}
  {-# REWRITE iβRSA-ENCRYPT_,_::_* #-}
  {-# REWRITE iβRSA-DECRYPT_,_::_* #-}
  {-# REWRITE iβPAILLIER-ENCRYPT_,_::_* #-}
  {-# REWRITE iβPAILLIER-DECRYPT_,_::_* #-}
  {-# REWRITE iβOPE-ENCRYPT::_* #-}
  {-# REWRITE iβOPE-DECRYPT::_* #-}
  {-# REWRITE iβELGAMAL-ENCRYPT_::_* #-}
  {-# REWRITE iβELGAMAL-DECRYPT_::_* #-}
  {-# REWRITE iβINCREMENT100_::_* #-}
  {-# REWRITE iβCRYPT-INCREMENT100_,_,_::_* #-}


  unquoteDecl indHistory = generateIndHit (vArg indHistory)
                                     (quote History)
                                     (quote indHistory*) 0 Recpoints Recpaths


  unquoteDecl βindHistory-paiHom = generateβIndHitPath (quote indHistory)
                                     ((vArg βindHistory-paiHom) ∷ [])
                                     (quote History)
                                     (quote indHistory*) 0 Recpoints Recpaths


  postulate
    paillier-rec-hom : (p q : Nat) → (i : Nat) → (vec : List Int) → (paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q)) vec ≡
                                                                     (increment-100 i) vec


  {-# TERMINATING #-}
  replay' : {m n : Nat} → History m n → List Int
  replay' {m} {n} r = recHistory* r (List Int) [] (λ r ls → id (replay' r))
                                              (λ val i r ls → insert val i (replay' r))
                                              (λ i r ls → delete i (replay' r))
                                              (λ p q r ls → rsa-encrypt p q (replay' r))
                                              (λ p q r ls → rsa-decrypt p q (replay' r))
                                              (λ p q r ls → paillier-encrypt p q (replay' r))
                                              (λ p q r ls → paillier-decrypt p q (replay' r))
                                              (λ r ls → ope-encrypt (replay' r))
                                              (λ r ls → ope-decrypt (replay' r))
                                              (λ p r ls → ElGamal-encrypt2 p (ElGamal-encrypt p (replay' r)))
                                              (λ p r ls → ElGamal-decrypt p (ElGamal-decrypt2 p (replay' r)))
                                              (λ i r ls → increment-100 i (replay' r))
                                              (λ p q i r ls → crypt-increment-100 p q i (replay' r))

  replay : {n : Nat} → History 0 n → List Int
  replay {n} r = replay' {0} {n} r

  postulate
    paillier-rec-hom' : {m n : Nat} → (p q : Nat) → (i : Nat) → (r : History m n) → (paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q)) (replay' r) ≡
                                                                                     (increment-100 i) (replay' r)


  replayP' : {m n : Nat} → History m n → List Int
  replayP' {m} {n} r = recHistory r (List Int) [] (λ r ls → id (replay' r))
                                              (λ val i r ls → insert val i (replay' r))
                                              (λ i r ls → delete i (replay' r))
                                              (λ p q r ls → rsa-encrypt p q (replay' r))
                                              (λ p q r ls → rsa-decrypt p q (replay' r))
                                              (λ p q r ls → paillier-encrypt p q (replay' r))
                                              (λ p q r ls → paillier-decrypt p q (replay' r))
                                              (λ r ls → ope-encrypt (replay' r))
                                              (λ r ls → ope-decrypt (replay' r))
                                              (λ p r ls → ElGamal-encrypt2 p (ElGamal-encrypt p (replay' r)))
                                              (λ p r ls → ElGamal-decrypt p (ElGamal-decrypt2 p (replay' r)))
                                              (λ i r ls → increment-100 i (replay' r))
                                              (λ p q i r ls → crypt-increment-100 p q i (replay' r))
                                              (λ p q i r → (paillier-rec-hom' p q i r))

  replayP : {n : Nat} → History 0 n → List Int
  replayP {n} r = replayP' {0} {n} r


  {-- I-history-paiHom-path : Interprets the insert-query path in cryptR as a path in the Universe given by insert function --}
  I-history-paiHom-path : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) →
                         ap replay (PAILLIER-HOMOMORPHISM_,_,_::_ p q i r) ≡ (paillier-rec-hom p q i (replay r))
  I-history-paiHom-path {n} p q i r = βrecHistory-paiHom (List Int) [] (λ r ls → id (replay' r))
                                              (λ val i r ls → insert val i (replay' r))
                                              (λ i r ls → delete i (replay' r))
                                              (λ p q r ls → rsa-encrypt p q (replay' r))
                                              (λ p q r ls → rsa-decrypt p q (replay' r))
                                              (λ p q r ls → paillier-encrypt p q (replay' r))
                                              (λ p q r ls → paillier-decrypt p q (replay' r))
                                              (λ r ls → ope-encrypt (replay' r))
                                              (λ r ls → ope-decrypt (replay' r))
                                              (λ p r ls → ElGamal-encrypt2 p (ElGamal-encrypt p (replay' r)))
                                              (λ p r ls → ElGamal-decrypt p (ElGamal-decrypt2 p (replay' r)))
                                              (λ i r ls → increment-100 i (replay' r))
                                              (λ p q i r ls → crypt-increment-100 p q i (replay' r))
                                              (λ p q i r → (paillier-rec-hom p q i (replay' r)))



open History_hit public

module Document_hit where

{-- cryptR : Higher inductive type representing the database tables as points and encryption, decryption functions and queries as paths --}

  postulate
    cryptR : Set
    ctab_ : {n : Nat} → History 0 n → cryptR
    ctabRSA_ : {n : Nat} → History 0 n → cryptR
    ctabPL_ : {n : Nat} → History 0 n → cryptR
    ctabOPE_ : {n : Nat} → History 0 n → cryptR
    ctabEG_ : {n : Nat} → History 0 n → cryptR
    insert-query : {n : Nat} → (value : Int) → (i : Nat) → (r : History 0 n) → (ctab r) ≡ (ctab (INSERT value at i :: r))
    delete-query : {n : Nat} → (i : Nat) → (r : History 0 (suc n)) → (ctab r) ≡ (ctab (DELETE i :: r))
    rsa-enc : {n : Nat} → (p : Nat) → (q : Nat) → (r : History 0 n) → (ctab r) ≡ (ctabRSA (RSA-ENCRYPT p , q :: r))
    rsa-dec : {n : Nat} → (p : Nat) → (q : Nat) → (r : History 0 n) → (ctabRSA r) ≡ (ctab (RSA-DECRYPT p , q :: r))
    paillier-enc : {n : Nat} → (p : Nat) → (q : Nat) → (r : History 0 n) → (ctab r) ≡ (ctabPL (PAILLIER-ENCRYPT p , q :: r))
    paillier-dec : {n : Nat} → (p : Nat) → (q : Nat) → (r : History 0 n) → (ctabPL r) ≡ (ctab (PAILLIER-DECRYPT p , q :: r))
    ope-enc : {n : Nat} → (r : History 0 n) → (ctab r) ≡ (ctabOPE (OPE-ENCRYPT:: r))
    ope-dec : {n : Nat} → (r : History 0 n) → (ctabPL r) ≡ (ctab (OPE-DECRYPT:: r))
    elgamalrsa-enc : {n : Nat} → (p : Nat) → (r : History 0 n) → (ctabRSA r) ≡ (ctabEG (ELGAMAL-ENCRYPT p :: r))
    elgamalrsa-dec : {n : Nat} → (p : Nat) → (r : History 0 n) → (ctabEG r) ≡ (ctabRSA (ELGAMAL-DECRYPT p :: r))
    elgamalope-enc : {n : Nat} → (p : Nat) → (r : History 0 n) → (ctabOPE r) ≡ (ctabEG (ELGAMAL-ENCRYPT p :: r))
    elgamalope-dec : {n : Nat} → (p : Nat) → (r : History 0 n) → (ctabEG r) ≡ (ctabOPE (ELGAMAL-DECRYPT p :: r))
    increment-by-100 : {n : Nat} → (i : Nat) → (r : History 0 n) → (ctab r) ≡ (ctab (INCREMENT100 i :: r))
    crypt-increment-by-100 : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) → (ctabPL r) ≡ (ctabPL (CRYPT-INCREMENT100 p , q , i :: r))
    id-cryptR : {n : Nat} → (r : History 0 n) → (ctab r) ≡ (ctab (ID-R:: r))

  cryptRpoints : List Name
  cryptRpoints = ((quote ctab_) ∷ (quote ctabRSA_) ∷ (quote ctabPL_) ∷ (quote ctabOPE_) ∷ (quote ctabEG_) ∷ [])

  cryptRpaths : List Name
  cryptRpaths = ((quote insert-query) ∷ (quote delete-query) ∷ (quote rsa-enc) ∷ (quote rsa-dec) ∷
                 (quote paillier-enc) ∷ (quote paillier-dec) ∷ (quote ope-enc) ∷ (quote ope-dec) ∷
                 (quote elgamalrsa-enc) ∷ (quote elgamalrsa-dec) ∷ (quote elgamalope-enc) ∷ (quote elgamalope-dec) ∷
                 (quote increment-by-100) ∷ (quote crypt-increment-by-100) ∷ (quote id-cryptR) ∷ [])


  unquoteDecl reccryptR* βctab_* βctabRSA_* βctabPL_* βctabOPE_* βctabEG_*
                                = generateβRec (vArg reccryptR*)
                                     ((vArg βctab_*) ∷ (vArg βctabRSA_*) ∷ (vArg βctabPL_*) ∷ (vArg βctabOPE_*) ∷ (vArg βctabEG_*) ∷ [])
                                     (quote cryptR) 0 cryptRpoints

  {-# REWRITE βctab_* #-}
  {-# REWRITE βctabRSA_* #-}
  {-# REWRITE βctabPL_* #-}
  {-# REWRITE βctabOPE_* #-}
  {-# REWRITE βctabEG_* #-}

  unquoteDecl reccryptR = generateRecHit (vArg reccryptR)
                                     (quote cryptR)
                                     (quote reccryptR*) 0 cryptRpoints cryptRpaths

  unquoteDecl βreccryptR-insertQ βreccryptR-deleteQ βreccryptR-rsaE βreccryptR-rsaD βreccryptR-paillierE βreccryptR-paillierD
              βreccryptR-OPEE βreccryptR-OPED βreccryptR-ElgRSAE βreccryptR-ElgRSAD βreccryptR-ElgOPEE βreccryptR-ElgOPED
              βreccryptR-increment100 βreccryptR-crypt-inc βreccryptR-id
              = generateβRecHitPath (quote reccryptR)
                                    ((vArg βreccryptR-insertQ) ∷ (vArg βreccryptR-deleteQ) ∷ (vArg βreccryptR-rsaE) ∷ (vArg βreccryptR-rsaD) ∷
                                     (vArg βreccryptR-paillierE) ∷ (vArg βreccryptR-paillierD) ∷
                                     (vArg βreccryptR-OPEE) ∷ (vArg βreccryptR-OPED) ∷
                                     (vArg βreccryptR-ElgRSAE) ∷ (vArg βreccryptR-ElgRSAD) ∷ (vArg βreccryptR-ElgOPEE) ∷ (vArg βreccryptR-ElgOPED) ∷
                                     (vArg βreccryptR-increment100) ∷ (vArg βreccryptR-crypt-inc) ∷ (vArg βreccryptR-id) ∷ [])
                                    (quote cryptR)
                                    (quote reccryptR*) 0 cryptRpoints cryptRpaths

-- -----

  unquoteDecl indcryptR* iβctab_* iβctabRSA_* iβctabPL_* iβctabOPE_* iβctabEG_*
                                = generateβInd (vArg indcryptR*)
                                     ((vArg iβctab_*) ∷ (vArg iβctabRSA_*) ∷ (vArg iβctabPL_*) ∷ (vArg iβctabOPE_*) ∷ (vArg iβctabEG_*) ∷ [])
                                     (quote cryptR) 0 cryptRpoints

  {-# REWRITE iβctab_* #-}
  {-# REWRITE iβctabRSA_* #-}
  {-# REWRITE iβctabPL_* #-}
  {-# REWRITE iβctabOPE_* #-}
  {-# REWRITE iβctabEG_* #-}

  unquoteDecl indcryptR = generateIndHit (vArg indcryptR)
                                     (quote cryptR)
                                     (quote indcryptR*) 0 cryptRpoints cryptRpaths

  unquoteDecl βindcryptR-insertQ βindcryptR-deleteQ βindcryptR-rsaE βindcryptR-rsaD βindcryptR-paillierE βindcryptR-paillierD
              βindcryptR-OPEE βindcryptR-OPED βindcryptR-ElgRSAE βindcryptR-ElgRSAD βindcryptR-ElgOPEE βindcryptR-ElgOPED
              βindcryptR-increment100 βindcryptR-crypt-inc βindcryptR-id
              = generateβIndHitPath (quote indcryptR)
                                    ((vArg βindcryptR-insertQ) ∷ (vArg βindcryptR-deleteQ) ∷ (vArg βindcryptR-rsaE) ∷ (vArg βindcryptR-rsaD) ∷
                                     (vArg βindcryptR-paillierE) ∷ (vArg βindcryptR-paillierD) ∷ (vArg βindcryptR-OPEE) ∷ (vArg βindcryptR-OPED) ∷
                                     (vArg βindcryptR-ElgRSAE) ∷ (vArg βindcryptR-ElgRSAD) ∷ (vArg βindcryptR-ElgOPEE) ∷ (vArg βindcryptR-ElgOPED) ∷
                                     (vArg βindcryptR-increment100) ∷ (vArg βindcryptR-crypt-inc) ∷ (vArg βindcryptR-id) ∷ [])
                                    (quote cryptR)
                                    (quote indcryptR*) 0 cryptRpoints cryptRpaths


  paillier-homRToC : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) → (ctab  (PAILLIER-DECRYPT p , q :: (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))
                                                                                   ≡ (ctab (INCREMENT100 i :: r))
  paillier-homRToC p q i r = ! ((paillier-enc p q r) ∘ (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ∘ (increment-by-100 i r)

  postulate
    paillier-homRecToCDB : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) →
                           ap ctab_ (PAILLIER-HOMOMORPHISM_,_,_::_ p q i r) ≡ paillier-homRToC p q i r


  I-cryptR : cryptR → Set
  I-cryptR r = reccryptR r Set (λ x → (Singleton (replay x)))
                                 (λ x → (Singleton (replay x)))
                                 (λ x → (Singleton (replay x)))
                                 (λ x → (Singleton (replay x)))
                                 (λ x → (Singleton (replay x)))
                                 (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                 (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                 (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                 (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                 (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                 (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                 (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                 (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                 (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                  (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                 (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                      (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                 (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                  (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                 (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                      (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                 (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                 (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                 (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

open Document_hit public


{-- I-cryptR-insert-path : Interprets the insert-query path in cryptR as a path in the Universe given by insert function --}
I-cryptR-insert-path : {n : Nat} → (value : Int) → (i : Nat) → (r : History 0 n) →
                       ap I-cryptR (insert-query value i r) ≡ ua (singleton-equiv {List Int} {List Int} {(insert value i)} (to-Singleton (insert value i)))
I-cryptR-insert-path value i r = βreccryptR-insertQ Set (λ x → (Singleton (replay x)))
                                                         (λ x → (Singleton (replay x)))
                                                         (λ x → (Singleton (replay x)))
                                                         (λ x → (Singleton (replay x)))
                                                         (λ x → (Singleton (replay x)))
                                                         (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                         (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                         (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                         (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                       (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                       (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                       (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                       (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                         (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                         (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                         (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))
                                                         
{-- I-cryptR-delete-path : Interprets the delete-query path in cryptR as a path in the Universe given by delete function --}
I-cryptR-delete-path : {n : Nat} → (i : Nat) → (r : History 0 (suc n)) →
                       ap I-cryptR (delete-query i r) ≡ ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i)))
I-cryptR-delete-path i r = βreccryptR-deleteQ Set (λ x → (Singleton (replay x)))
                                                   (λ x → (Singleton (replay x)))
                                                   (λ x → (Singleton (replay x)))
                                                   (λ x → (Singleton (replay x)))
                                                   (λ x → (Singleton (replay x)))
                                                   (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                   (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                   (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                   (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                   (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                   (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                   (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                   (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                   (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                       (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                   (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                       (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                   (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                       (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                   (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                       (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                   (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                   (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                   (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-rsa-enc : Interprets the rsa-enc path in cryptR as a path in the Universe given by rsa-encrypt function --}
I-cryptR-rsa-enc : {n : Nat} → (p q : Nat) → (r : History 0 n) → ap I-cryptR (rsa-enc p q r) ≡ ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q)))
I-cryptR-rsa-enc p q r = βreccryptR-rsaE Set (λ x → (Singleton (replay x)))
                                             (λ x → (Singleton (replay x)))
                                             (λ x → (Singleton (replay x)))
                                             (λ x → (Singleton (replay x)))
                                             (λ x → (Singleton (replay x)))
                                             (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                             (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                             (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                             (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                             (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                             (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                             (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                             (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                             (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                           (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                             (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                           (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                             (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                           (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                             (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                           (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                             (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                             (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                             (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-rsa-dec : Interprets the rsa-dec path in cryptR as a path in the Universe given by rsa-decrypt function --}
I-cryptR-rsa-dec : {n : Nat} → (p q : Nat) → (r : History 0 n) →
                   ap I-cryptR (rsa-dec p q r) ≡ ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q)))
I-cryptR-rsa-dec p q r = βreccryptR-rsaD Set (λ x → (Singleton (replay x)))
                                             (λ x → (Singleton (replay x)))
                                             (λ x → (Singleton (replay x)))
                                             (λ x → (Singleton (replay x)))
                                             (λ x → (Singleton (replay x)))
                                             (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                             (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                             (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                             (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                             (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                             (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                             (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                             (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                             (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                 (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                             (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                 (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                             (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                 (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                             (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                 (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                             (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                             (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                             (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-paillier-path : Interprets the paillier-enc path in cryptR as a path in the Universe given by paillier-encrypt function --}
I-cryptR-paillier-enc : {n : Nat} → (p q : Nat) → (r : History 0 n) →
                        ap I-cryptR (paillier-enc p q r) ≡ ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q)))
I-cryptR-paillier-enc p q r = βreccryptR-paillierE Set (λ x → (Singleton (replay x)))
                                                       (λ x → (Singleton (replay x)))
                                                       (λ x → (Singleton (replay x)))
                                                       (λ x → (Singleton (replay x)))
                                                       (λ x → (Singleton (replay x)))
                                                       (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                       (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                       (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                       (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                       (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                       (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                       (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                       (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                       (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                          (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                       (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                          (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                       (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                          (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                       (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                          (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                       (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                       (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                       (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-paillier-path-inv : Interprets the paillier-dec path in cryptR as a path in the Universe given by paillier-decrypt function --}
I-cryptR-paillier-dec : {n : Nat} → (p q : Nat) → (r : History 0 n) →
                        ap I-cryptR (paillier-dec p q r) ≡ ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q)))
I-cryptR-paillier-dec p q r = βreccryptR-paillierD Set (λ x → (Singleton (replay x)))
                                                       (λ x → (Singleton (replay x)))
                                                       (λ x → (Singleton (replay x)))
                                                       (λ x → (Singleton (replay x)))
                                                       (λ x → (Singleton (replay x)))
                                                       (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                       (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                       (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                       (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                       (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                       (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                       (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                       (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                       (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                          (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                       (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                          (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                       (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                          (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                       (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                          (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                       (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                       (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                       (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-ope-enc : Interprets the ope-enc path in cryptR as a path in the Universe given by ope-encrypt function --}
I-cryptR-ope-enc : {n : Nat} → (r : History 0 n) →
                   ap I-cryptR (ope-enc r) ≡ ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt))
I-cryptR-ope-enc r = βreccryptR-OPEE Set (λ x → (Singleton (replay x)))
                                         (λ x → (Singleton (replay x)))
                                         (λ x → (Singleton (replay x)))
                                         (λ x → (Singleton (replay x)))
                                         (λ x → (Singleton (replay x)))
                                         (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                         (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                         (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                         (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                            (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                            (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                            (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                            (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                         (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                         (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                         (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-ope-dec : Interprets the ope-dec path in cryptR as a path in the Universe given by ope-decrypt function --}
I-cryptR-ope-dec : {n : Nat} → (r : History 0 n) →
                   ap I-cryptR (ope-dec r) ≡ ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt))
I-cryptR-ope-dec r = βreccryptR-OPED Set (λ x → (Singleton (replay x)))
                                         (λ x → (Singleton (replay x)))
                                         (λ x → (Singleton (replay x)))
                                         (λ x → (Singleton (replay x)))
                                         (λ x → (Singleton (replay x)))
                                         (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                         (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                         (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                         (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                            (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                            (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                            (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                            (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                         (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                         (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                         (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-elgamalrsa-path : Interprets the elgamalrsa-enc path in cryptR as a path in the Universe given by ElGamal-encrypt function --}
I-cryptR-elgamalrsa-enc : {n : Nat} → (p : Nat) → (r : History 0 n) →
                          ap I-cryptR (elgamalrsa-enc p r) ≡ ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                  (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p))))
I-cryptR-elgamalrsa-enc p r = βreccryptR-ElgRSAE Set (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                     (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-elgamalrsa-dec : Interprets the elgamalrsa-dec path in cryptR as a path in the Universe given by ElGamal-decrypt function --}
I-cryptR-elgamalrsa-dec : {n : Nat} → (p : Nat) → (r : History 0 n) →
                          ap I-cryptR (elgamalrsa-dec p r) ≡ ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                      (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p))))
I-cryptR-elgamalrsa-dec p r = βreccryptR-ElgRSAD Set (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                     (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-elgamalope-enc : Interprets the elgamalope-enc path in cryptR as a path in the Universe given by ElGamal-encrypt function --}
I-cryptR-elgamalope-enc : {n : Nat} → (p : Nat) → (r : History 0 n) →
                           ap I-cryptR (elgamalope-enc p r) ≡ ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                  (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p))))
I-cryptR-elgamalope-enc p r = βreccryptR-ElgOPEE Set (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                     (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-elgamalope-dec : Interprets the elgamalope-dec path in cryptR as a path in the Universe given by ElGamal-decrypt function --}
I-cryptR-elgamalope-dec : {n : Nat} → (p : Nat) → (r : History 0 n) →
                          ap I-cryptR (elgamalope-dec p r) ≡ ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                      (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p))))
I-cryptR-elgamalope-dec p r = βreccryptR-ElgOPED Set (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                     (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-increment100-path : Interprets the increment-by-100 path in cryptR as a path in the Universe given by increment-100 function --}
I-cryptR-increment100-path : {n : Nat} → (i : Nat) → (r : History 0 n) →
                             ap I-cryptR (increment-by-100 i r) ≡ ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i)))
I-cryptR-increment100-path i r = βreccryptR-increment100 Set (λ x → (Singleton (replay x)))
                                                              (λ x → (Singleton (replay x)))
                                                              (λ x → (Singleton (replay x)))
                                                              (λ x → (Singleton (replay x)))
                                                              (λ x → (Singleton (replay x)))
                                                              (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                              (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                              (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                              (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                              (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                              (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                              (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                              (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                              (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                            (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                              (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                            (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                              (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                            (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                              (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                            (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                              (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                              (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                              (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-crypt-increment100-path : Interprets the crypt-increment-by-100 path in cryptR as a path in the Universe given by crypt-increment-100 function --}
I-cryptR-crypt-increment100-path : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) →
                                   ap I-cryptR (crypt-increment-by-100 p q i r) ≡ ua (singleton-equiv {List Int} {List Int}
                                                                                                         {(crypt-increment-100 p q i)}
                                                                                                         (to-Singleton (crypt-increment-100 p q i)))
I-cryptR-crypt-increment100-path p q i r = βreccryptR-crypt-inc Set (λ x → (Singleton (replay x)))
                                                                     (λ x → (Singleton (replay x)))
                                                                     (λ x → (Singleton (replay x)))
                                                                     (λ x → (Singleton (replay x)))
                                                                     (λ x → (Singleton (replay x)))
                                                                     (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                                     (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-id : Identity function for cryptR --}
I-cryptR-id : {n : Nat} → (r : History 0 n) → ap I-cryptR (id-cryptR r) ≡ ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id))
I-cryptR-id r = βreccryptR-id Set (λ x → (Singleton (replay x)))
                                   (λ x → (Singleton (replay x)))
                                   (λ x → (Singleton (replay x)))
                                   (λ x → (Singleton (replay x)))
                                   (λ x → (Singleton (replay x)))
                                   (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                   (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                   (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                   (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                   (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                   (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                   (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                   (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                   (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                       (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                   (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                       (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                   (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                       (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                   (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                       (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                   (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                   (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                   (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))


{-- Path representing the homotopy of Paillier homomorphic property --}  
paillier-homotopy : {n : Nat} → (p q : Nat) (i : Nat) → (r : History 0 n) →
                      transport (λ x → ctab r ≡ ctab x) (PAILLIER-HOMOMORPHISM p , q , i :: r)
                                ((paillier-enc p q r) ∘
                                (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))
                      ≡ (increment-by-100 i r)
paillier-homotopy p q i r = transport (λ x → ctab r ≡ ctab x) (PAILLIER-HOMOMORPHISM p , q , i :: r)
                                ((paillier-enc p q r) ∘
                                (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ≡⟨ transport' ctab_ (PAILLIER-HOMOMORPHISM p , q , i :: r)
                                                                                                                       (((paillier-enc p q r) ∘
                                                                                                                       (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                                                                                                       (paillier-dec p q (CRYPT-INCREMENT100 p , q , i ::
                                                                                                                       (PAILLIER-ENCRYPT p , q :: r))))) ⟩
                                ((paillier-enc p q r) ∘
                                (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ∘
                                (ap ctab_ (PAILLIER-HOMOMORPHISM p , q , i :: r)) ≡⟨ ap (λ x → ((paillier-enc p q r) ∘
                                                                                                  (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                                                                                  (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ∘ x)
                                                                                          (paillier-homRecToCDB p q i r) ⟩
                                ((paillier-enc p q r) ∘
                                (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ∘
                                ! ((paillier-enc p q r) ∘ (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ∘ (increment-by-100 i r)
                                ≡⟨ assocP ((paillier-enc p q r) ∘
                                            (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                            (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))
                                          (! ((paillier-enc p q r) ∘
                                              (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                              (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))))
                                              (increment-by-100 i r) ⟩
                                (((paillier-enc p q r) ∘
                                (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ∘
                                ! ((paillier-enc p q r) ∘ (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))) ∘ (increment-by-100 i r)
                                ≡⟨ ap (λ x → x ∘ (increment-by-100 i r))
                                      (invTransR ((paillier-enc p q r) ∘
                                                  (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                                  (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))) ⟩
                                refl ∘ (increment-by-100 i r) ≡⟨ ! (unitTransL (increment-by-100 i r)) ⟩
                                (increment-by-100 i r) ∎


{-- I-hom-paillier1 : Maps the part 1 of Paillier homomorphism into the Universe --}
I-hom-paillier1' : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) →
                    ap I-cryptR ((paillier-enc p q r) ∘ (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                 (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))
                    ≡ (ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))}
                                            (to-Singleton (paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q)))))
I-hom-paillier1' {n} p q i r =  ap I-cryptR ((paillier-enc p q r) ∘ (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                 (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ≡⟨ apfTrans I-cryptR
                                                                       (paillier-enc p q r) ((crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r) ∘
                                                                       (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))) ⟩
                                (ap I-cryptR (paillier-enc p q r)) ∘ (ap I-cryptR ((crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))) ≡⟨ ap (λ x → (ap I-cryptR (paillier-enc p q r)) ∘ x)
                                                                              (apfTrans I-cryptR ((crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)))
                                                                              (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ⟩
                                ap I-cryptR (paillier-enc p q r) ∘
                                ap I-cryptR (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                ap I-cryptR (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))) ≡⟨ ap
                                                                                            (λ x → x ∘ ap I-cryptR (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                                                                            ap I-cryptR (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))
                                                                                            (I-cryptR-paillier-enc p q r) ⟩
                                (ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q)))) ∘
                                ap I-cryptR (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                ap I-cryptR (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))) ≡⟨ ap
                                                                                            (λ x → (ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)}
                                                                                                        (to-Singleton (paillier-encrypt p q)))) ∘ x ∘
                                                                                                        ap I-cryptR (paillier-dec p q (CRYPT-INCREMENT100 p , q , i ::
                                                                                                                    (PAILLIER-ENCRYPT p , q :: r))))
                                                                                            (I-cryptR-crypt-increment100-path p q i (PAILLIER-ENCRYPT p , q :: r)) ⟩
                                (ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q)))) ∘
                                (ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i)))) ∘ 
                                ap I-cryptR (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))) ≡⟨ ap
                                                                                            (λ x → (ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)}
                                                                                                        (to-Singleton (paillier-encrypt p q)))) ∘
                                                                                                   (ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)}
                                                                                                       (to-Singleton (crypt-increment-100 p q i)))) ∘ x)
                                                                                            ((I-cryptR-paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ⟩
                                (ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q)))) ∘
                                (ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i)))) ∘ 
                                (ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                ≡⟨ assocP (ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                          (ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                          (ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q)))) ⟩
                                ((ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} {(replay r)} (to-Singleton (paillier-encrypt p q)))) ∘
                                (ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} {(replay (PAILLIER-ENCRYPT p , q :: r))} (to-Singleton (crypt-increment-100 p q i))))) ∘ 
                                (ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                ≡⟨ ap (λ x → x ∘ (ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q)))))
                                      (! (ua-∘e' {List Int} {List Int} {List Int} {(paillier-encrypt p q)} {(crypt-increment-100 p q i)} {(replay r)}
                                               (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q)))
                                               (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))) ⟩
                                (ua (_∘e'_ {List Int} {List Int} {List Int} {(crypt-increment-100 p q i)} {(paillier-encrypt p q)} {(replay r)}
                                           (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} {(replay (PAILLIER-ENCRYPT p , q :: r))}
                                                            (to-Singleton (crypt-increment-100 p q i)))
                                           (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} {(replay r)} (to-Singleton (paillier-encrypt p q))))) ∘ 
                                (ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                ≡⟨ ap (λ x → x ∘ (ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q)))))
                                      (ap ua refl) ⟩
                                (ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i) ○ (paillier-encrypt p q)} {(replay r)}
                                    (to-Singleton ((crypt-increment-100 p q i) ○ (paillier-encrypt p q))))) ∘
                                (ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                ≡⟨ (! (ua-∘e' {List Int} {List Int} {List Int} {(crypt-increment-100 p q i) ○ (paillier-encrypt p q)} {(paillier-decrypt p q)}  {(replay r)}
                                               (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i) ○ (paillier-encrypt p q)} {(replay r)}
                                                               (to-Singleton ((crypt-increment-100 p q i) ○ (paillier-encrypt p q))))
                                               (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))) ⟩
                                (ua (_∘e'_ {List Int} {List Int} {List Int} {(paillier-decrypt p q)} {(crypt-increment-100 p q i) ○ (paillier-encrypt p q)} {(replay r)}
                                           (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q)))
                                           (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i) ○ (paillier-encrypt p q)}
                                               (to-Singleton ((crypt-increment-100 p q i) ○ (paillier-encrypt p q))))))
                                ≡⟨ ap ua refl ⟩
                                (ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))}
                                            (to-Singleton (paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))))) ∎


{-- I-hom-paillier1 : Maps the part 1 of Paillier homomorphism into the Universe --}

I-hom-paillier1 : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) →
                    (transport (λ x → Singleton (replay r) ≡ Singleton (replay x)) (PAILLIER-HOMOMORPHISM p , q , i :: r)
                                 (ap I-cryptR  ((paillier-enc p q r) ∘
                                 (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                 (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))))
                    ≡ (transport (λ x → Singleton (replay r) ≡ Singleton (replay x)) (PAILLIER-HOMOMORPHISM p , q , i :: r) -- (paillier-hom2* p q i r)
                         (ua (singleton-equiv {List Int} {List Int}
                                           {(paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))}
                                           (to-Singleton (paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))))))
I-hom-paillier1 p q i r = (transport (λ x → Singleton (replay r) ≡ Singleton (replay x)) (PAILLIER-HOMOMORPHISM p , q , i :: r)
                                 (ap I-cryptR  ((paillier-enc p q r) ∘
                                 (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                 (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))))
                    ≡⟨ ap (transport (λ x → Singleton (replay r) ≡ Singleton (replay x)) (PAILLIER-HOMOMORPHISM p , q , i :: r)) (I-hom-paillier1' p q i r) ⟩
                    (transport (λ x → Singleton (replay r) ≡ Singleton (replay x)) (PAILLIER-HOMOMORPHISM p , q , i :: r)
                         (ua (singleton-equiv {List Int} {List Int}
                                           {(paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))}
                                           (to-Singleton (paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q)))))) ∎

{-- I-hom-paillier2 : Maps the part 2 of Paillier homomorphism into the Universe --}
I-hom-paillier2 : {n : Nat} → (i : Nat) → (r : History 0 n) → ap I-cryptR (increment-by-100 i r) ≡ ua (singleton-equiv {List Int} {List Int} {(increment-100 i)}
                                                                                                         (to-Singleton (increment-100 i)))
I-hom-paillier2 i r = I-cryptR-increment100-path i r


postulate
  {-- Paillier homomorphism --}
  paillier-hom* : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) →  (Singleton ((paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q)) (replay r))) ≡
                                                                                       (Singleton ((increment-100 i) (replay r)))


{-- paillier-hom : Representation of Paillier homomorphism in the Universe --}
paillier-hom : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) →
                  (transport (λ x → Singleton (replay r) ≡ Singleton (replay x)) (PAILLIER-HOMOMORPHISM p , q , i :: r) 
                     (ua (singleton-equiv {List Int} {List Int}
                                          {(paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))}
                                          (to-Singleton (paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))))))
                 ≡  (ua (singleton-equiv {List Int} {List Int}
                                          {(increment-100 i)}
                                          (to-Singleton (increment-100 i))))
paillier-hom p q i r = (transport (λ x → Singleton (replay r) ≡ Singleton (replay x)) (PAILLIER-HOMOMORPHISM p , q , i :: r) 
                                  (ua (singleton-equiv {List Int} {List Int}
                                      {(paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))}
                                      (to-Singleton (paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q)))))) ≡⟨ ! (I-hom-paillier1 p q i r) ⟩
                                  (transport (λ x → Singleton (replay r) ≡ Singleton (replay x)) (PAILLIER-HOMOMORPHISM p , q , i :: r)
                                             (ap I-cryptR  ((paillier-enc p q r) ∘
                                                            (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                                            (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))))
                                                            ≡⟨ ap' (ap I-cryptR) {(PAILLIER-HOMOMORPHISM p , q , i :: r)} (paillier-homotopy p q i r) ⟩
                                  (ap I-cryptR (increment-by-100 i r)) ≡⟨ (I-hom-paillier2 i r) ⟩
                                  (ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i)))) ∎

postulate

  {-- I-cryptR-paillier-homotopy : Mapping of the Paillier homomorphism homotopy in cryptR into the Universe given by paillier-hom --}
  I-cryptR-paillier-homotopy : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) → 
                                 (ap' (ap I-cryptR) {(PAILLIER-HOMOMORPHISM p , q , i :: r)} (paillier-homotopy p q i r))
                                 ≡
                                 (I-hom-paillier1 p q i r) ∘ (paillier-hom p q i r) ∘ ! (I-hom-paillier2 i r)

{-- Interpreters which converts the given queries into functions acting on types in the Universe --}

{-- Interpreters to map the paths into the Universe --}

interp#1 : {a b : cryptR} → (p : a ≡ b) → (I-cryptR a) ≃ (I-cryptR b)
interp#1 p = coe-biject (ap I-cryptR p) 

interp#2 : {a b : cryptR} → (p : a ≡ b) → (I-cryptR a) → (I-cryptR b)
interp#2 p = coe' (ap I-cryptR p) 

{-- Interpreters to map the homotopies into the Universe --}

interp#3 : {a b : cryptR} → {p q : a ≡ b} → (x : p ≡ q) → (I-cryptR a ≡ I-cryptR b) ≃ (I-cryptR a ≡ I-cryptR b)
interp#3 {a} {b} {p} {q} x = coe-biject (apI-path I-cryptR x)

interp#4 : {a b : cryptR} → {p q : a ≡ b} → (x : p ≡ q) → (I-cryptR a ≡ I-cryptR b) → (I-cryptR a ≡ I-cryptR b)
interp#4 x = coe' (apI-path I-cryptR x)

