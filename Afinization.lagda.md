---
title: Formalizing Affinitization of a Projective Plane in Agda
author: G. Calderón

---





<!--  
imports and module definition (hiden)
```agda
module Afinization where
open import Level
open import Relation.Nullary
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Function
     using (case_of_ ; _$_ ; _∘_)
open import Relation.Binary.Apartness
```
-->


# von Plato Constructive Geometry


## Lines and Points

```agda
record ApartnessGeometry
     : Set₁ where
  field

    Point : Set
    Line  : Set
```

## Basic Relations in Apartness Geometry



*  `DiPt P Q` -  The points `P` and `Q` are distinct.
*  `DiPT r s` - The lines `r` and `s` are distinct.
*  `Con r s`  - The lines `r` and `s` are convergente (nonparellel)
*  `Apt P r`  - The point `P` is outside the line `r`. 



```agda
    DiPt  -- distinct points
          :  Point  →  Point  →  Set
    DiLn  -- distinct lines
          :   Line   →  Line   →  Set
    Con   -- convergent lines
          :  Line   →  Line   →  Set
    Apt   -- point outside line
          :  Point  →  Line   →  Set
```


```agda
  EqPt      :   Point → Point → Set
  EqPt P Q  =   ¬ (DiPt P Q)

  EqLn      :   Line → Line → Set
  EqLn r s  =   ¬ (DiLn r s)

  Par       :   Line → Line → Set
  Par r s   =   ¬ (Con r s)

  Inc       :   Point → Line → Set
  Inc P r   =   ¬ (Apt P r)
```


## Axioms for apartness, convergence and outside


### Irreflexivity

`DiPt`, `DiLn` and `Con`  are *irreflexive* relations:

```agda
  field
    irref-DiPt  :  ∀ {P}  →  ¬ (DiPt P P)
    irref-DiLn  :  ∀ {l}  →  ¬ (DiLn l l)
    irref-Con   :  ∀ {l}  →  ¬ (Con l l) 
```


### Cotransitivity

In addition, the *cotransitivity* holds for these relations:

```agda
    apartness-DiPt  :  ∀ {A B} C  →  DiPt A B  →  DiPt A C  ⊎  DiPt B C
    apartness-DiLn  :  ∀ {a b} c  →  DiLn a b  →  DiLn a c  ⊎  DiLn b c 
    apartness-Con   :  ∀ {a b} c  →  Con a b   →  Con a c   ⊎  Con b c   
```

### Line connecting two distinct points

There exists a line passing by two distinct points.

```agda
    ln : ∀ {A B : Point} → DiPt A B → Line
        
    ln-left   :  ∀   {A B} 
                 →  (A♯B : DiPt A B)
                    ------------------
                 → Inc A (ln A♯B)
                                
    ln-right  :  ∀   {A B} 
                 →  (A♯B : DiPt A B)
                     ----------------
                 →  Inc B (ln A♯B)
```


### Intersection point of two convergent lines

*  There is a point which belongs to two convergent lines.

```agda
    pt : ∀ {r s : Line} → Con r s → Point

    pt-left   :  ∀    {a b}
                 →   (a∦b : Con a b)
                      ---------------
                 →   Inc (pt a∦b) a
                                
    pt-right  :  ∀    {a b}
                 →   (a∦b : Con a b)
                    ----------------
                →    Inc (pt a∦b) b
```


### Equality and Rewriting


```agda
  field
    compat-Apt-EqPt : ∀ A B l → Apt A l → DiPt A B ⊎ Apt B l
    compat-Apt-EqLn : ∀ l m A → Apt A l → DiLn l m ⊎ Apt A m
    compat-Con-EqLn : ∀ l m n → Con l m → DiLn m n ⊎ Con l n
```


### Constructive uniqueness axiom for lines and points


```agda
    uniqueness : ∀ {A B l m}
         →   DiPt A B
         →   DiLn l m
         ---------------------
         →   Apt A l ⊎ Apt A m
                 ⊎
              Apt B l ⊎ Apt B m
```


The line built by `ln` is the only line passing by the two given points. 


```agda
  unq-ln :  ∀  {A B l}
            →  (A♯B : DiPt A B)
            →  Inc A l
            →  Inc B l
               ---------------------
            →  EqLn l (ln A♯B)
```


```agda
  unq-ln A♯B A∈l B∈l l♯AB 
         with uniqueness A♯B l♯AB
  ...    |  inj₁              A∉l      =  A∈l A∉l
  ...    |  inj₂ (inj₁        A∉AB )   =  ln-left A♯B A∉AB
  ...    |  inj₂ (inj₂ (inj₁  B∉l  ))  =  B∈l B∉l
  ...    |  inj₂ (inj₂ (inj₂  B∉AB ))  =  ln-right A♯B B∉AB
```



The substitution rule for `Apt` which follows from the axioms of compatibility: 


```agda
  subs-Apt₁ :  ∀  {A B l} →  Apt A l →  EqPt A B →  Apt B l
  subs-Apt₁ A∉l A=B   with   compat-Apt-EqPt _ _  _ A∉l
  ...   |      inj₁ A♯B  =  ⊥-elim (A=B A♯B)
  ...   |      inj₂ B∉l  =  B∉l
  subs-Apt₂ : ∀ {A l r} → Apt A l → EqLn l r → Apt A r
  subs-Apt₂ {r = r} A∉l l=r  with  compat-Apt-EqLn _ r _ A∉l
  ...   |  inj₁ l♯r  =  ⊥-elim (l=r l♯r)
  ...   |  inj₂ A∉r  =  A∉r
```


## Symmetry


```agda
  sym-DiPt  :  ∀ {A B}  → DiPt A B → DiPt B A
  sym-DiLn  :  ∀ {r s}  → DiLn r s → DiLn s r
  sym-Con   :  ∀ {r s}  → Con r s → Con s r
```

<!-- pruebas omitidas
```agda
  sym-DiPt {A} {B} A♯B =
    case apartness-DiPt A A♯B of
    \{ (inj₁ A♯A) → ⊥-elim (irref-DiPt A♯A)
     ; (inj₂ B♯A) → B♯A
     }

  sym-DiLn {r} {s} r♯s =
    case apartness-DiLn r r♯s of
    \{ (inj₁ r♯r) → ⊥-elim (irref-DiLn r♯r)
     ; (inj₂ s♯r) → s♯r
     }
```
-->



<!--  A lot of theorems, lemmas and propositions
```agda
  -- symmetry
  sym-Con {r} {s} r∦s =
    case apartness-Con r r∦s of
    \{ (inj₁ r∦r) → ⊥-elim (irref-Con r∦r)
     ; (inj₂ s∦r) → s∦r
     }

  sym-EqLn : ∀ {r s} → EqLn r s → EqLn s r
  sym-EqLn r=s = r=s ∘ sym-DiLn

  sym-EqPt : ∀ {A B} → EqPt A B → EqPt B A
  sym-EqPt A=B = A=B ∘ sym-DiPt


  -- susbtitution for Inc
  subs-Inc₁ : ∀ {A B l} → Inc A l → EqPt A B → Inc B l
  subs-Inc₁ A∈l A=B = λ B∉l → A∈l (subs-Apt₁ B∉l (sym-EqPt A=B))

  subs-Inc₂ : ∀ {r s A} → Inc A r → EqLn r s → Inc A s
  subs-Inc₂ A∈r r=s = λ A∉s → A∈r (subs-Apt₂ A∉s (sym-EqLn r=s))

  -- Theoreme 3.2
  Con→DiLn : ∀{l m} → Con l m → DiLn l m
  Con→DiLn {l} {m} l∤m =
    case compat-Con-EqLn l m l l∤m of
    \{ (inj₁ m≠l) → sym-DiLn m≠l
     ; (inj₂ l∤l) → ⊥-elim (irref-Con l∤l)
     }

  -- uniqueness of intersecion of convergent lines
  unq-pt : ∀{a b Q} → (a∦b : Con a b)
                    → Inc Q a
                    → Inc Q b
                    → EqPt Q (pt a∦b)
  unq-pt a∦b Q∈a Q∈b Q♯pt
      with uniqueness Q♯pt (Con→DiLn a∦b)
  ... | inj₁             Q∉A    = Q∈a Q∉A
  ... | inj₂ (inj₁       Q∉b  ) = Q∈b Q∉b
  ... | inj₂ (inj₂ (inj₁ pt∉a)) = pt-left _ pt∉a
  ... | inj₂ (inj₂ (inj₂ pt∉b)) = pt-right _ pt∉b


  -- Symmetry in apartness and incidence

  -- Lemma 4.1
  lemma-4-1-ln→ : ∀ {A B l} → (A≠B : DiPt A B)
                          → DiLn l (ln A≠B) → Apt A l ⊎ Apt B l
  lemma-4-1-ln→ A≠B  l≠AB =
        case uniqueness A≠B l≠AB of
        \{ (inj₁ A∉l) → inj₁ A∉l
         ; (inj₂ qq) →
           case qq of
           \{ (inj₁ A∉AB) → ⊥-elim (ln-left A≠B A∉AB)
            ; (inj₂ rr) →
              case rr of
              \{ (inj₁ B∉l) → inj₂ B∉l
               ; (inj₂ B∉AB) → ⊥-elim (ln-right A≠B B∉AB)
               }
            }
         }

  lemma-4-1-ln← : ∀ {A B l} → (A≠B : DiPt A B)
                  → Apt A l ⊎ Apt B l → DiLn l (ln A≠B)
  lemma-4-1-ln← {A} {B} {l} A≠B (inj₁ A∉l) =
    case  compat-Apt-EqLn  l (ln A≠B) A A∉l of
    \{ (inj₁ l≠AB) → l≠AB
     ; (inj₂ A∉AB) → ⊥-elim (ln-left A≠B A∉AB)
     }
  lemma-4-1-ln← {A} {B} {l} A≠B (inj₂ B∉l) =
    case  compat-Apt-EqLn  l (ln A≠B) B B∉l of
    \{ (inj₁ l≠AB) → l≠AB
     ; (inj₂ B∉AB) → ⊥-elim (ln-right A≠B B∉AB)
     }

  lemma-4-1-pt→ : ∀ {a b P} → (a∤b : Con a b)
                          → DiPt P (pt a∤b) → Apt P a ⊎ Apt P b
  lemma-4-1-pt→ a∤b  P≠ab =
        case uniqueness P≠ab (Con→DiLn a∤b) of
        \{ (inj₁ P∉A) → inj₁ P∉A
         ; (inj₂ qq) →
              case qq of
              \{ (inj₁ P∉b) → inj₂ P∉b
               ; (inj₂ pp) →
                 case pp of
                 \{ (inj₁ ab∉a) → ⊥-elim (pt-left a∤b ab∉a)
                  ; (inj₂ ab∉b) → ⊥-elim (pt-right a∤b ab∉b)
                  }
               }
         }

  lemma-4-1-pt← : ∀ {a b P} → (a∤b : Con a b)
                  → Apt P a ⊎ Apt P b → DiPt  P (pt a∤b)
  lemma-4-1-pt← {a} {b} {P} a∤b (inj₁ P∉a) =
        case compat-Apt-EqPt  P (pt a∤b) a P∉a of
        \{ (inj₁ P≠ab) → P≠ab
         ; (inj₂ ab∉a) → ⊥-elim (pt-left a∤b ab∉a)
         }
  lemma-4-1-pt← {a} {b} {P} a∤b (inj₂ P∉b) =
        case compat-Apt-EqPt P (pt a∤b) b P∉b of
        \{ (inj₁ P≠ab) → P≠ab
         ; (inj₂ ab∉b) → ⊥-elim (pt-right a∤b ab∉b)
         }

  -- Theorem 4.2 - Symmetry of Apt
  theorem-4-2 : ∀ {A B C D} → (A≠B : DiPt A B) → (C≠D : DiPt C D)
                →  Apt A (ln C≠D) ⊎ Apt B (ln C≠D)
                →  Apt C (ln A≠B) ⊎ Apt D (ln A≠B)
  theorem-4-2 A≠B C≠D Apt-A|B-CD  = lemma-4-1-ln→  _ AB≠CD
              where AB≠CD : DiLn (ln A≠B) (ln C≠D)
                    AB≠CD = sym-DiLn (lemma-4-1-ln← _ Apt-A|B-CD)

  lemma-4-3ᵢ :  ∀ {C A B}
               → (A≠B : DiPt A B) → Apt C (ln A≠B)
               → DiPt C A × DiPt C B
  lemma-4-3ᵢ {C} {A} {B} A≠B C∉AB with compat-Apt-EqPt _ A (ln A≠B) C∉AB
  lemma-4-3ᵢ {B = B} A≠B C∉AB | inj₁ C≠A
                      with compat-Apt-EqPt _ B (ln A≠B) C∉AB
  lemma-4-3ᵢ A≠B C∉AB | inj₁ C≠A | inj₁ C≠B = C≠A , C≠B
  lemma-4-3ᵢ A≠B C∉AB | inj₁ C≠A | inj₂ B∉AB = ⊥-elim (ln-right A≠B B∉AB)
  lemma-4-3ᵢ A≠B C∉AB | inj₂ A∉AB = ⊥-elim (ln-left A≠B A∉AB)

  lemma-4-3ᵢᵢ :  ∀ {C A B}
                 → (A≠B : DiPt A B) → (C∉AB : Apt C (ln A≠B))
                 → let l43ᵢ = lemma-4-3ᵢ A≠B C∉AB
                       C≠A  = proj₁ l43ᵢ
                       C≠B  = proj₂ l43ᵢ
                 in DiLn (ln A≠B) (ln C≠A) × DiLn (ln A≠B) (ln C≠B)
  lemma-4-3ᵢᵢ A≠B C∉AB = qed
    where l43ᵢ = lemma-4-3ᵢ A≠B C∉AB
          C≠A  = proj₁ l43ᵢ
          C≠B  = proj₂ l43ᵢ

          qed : DiLn (ln A≠B) (ln C≠A) × DiLn (ln A≠B) (ln C≠B)
          qed  with compat-Apt-EqLn (ln A≠B) (ln C≠A) _ C∉AB
          qed | inj₁ AB≠CA with compat-Apt-EqLn (ln A≠B) (ln C≠B) _ C∉AB
          qed | inj₁ AB≠CA | inj₁ AB≠CB = AB≠CA , AB≠CB
          qed | inj₁ AB≠CA | inj₂ C∉CB =  ⊥-elim (ln-left C≠B C∉CB)
          qed | inj₂ C∉CA = ⊥-elim (ln-left C≠A C∉CA)

  -- triangle axioms
  triangle₁ : ∀ {A B C} → (A≠B : DiPt A B)
                        → (C∉AB : Apt C (ln A≠B))
                        → let C≠B = proj₂ (lemma-4-3ᵢ A≠B C∉AB)
                          in Apt A (ln C≠B)
  triangle₁ {A} A≠B C∉AB = qed
     where
       C≠B = proj₂ (lemma-4-3ᵢ A≠B C∉AB)
       AB≠CB = proj₂ (lemma-4-3ᵢᵢ A≠B C∉AB)

       qed : Apt A (ln C≠B)
       qed with uniqueness  A≠B AB≠CB
       qed | inj₁ A∉AB = ⊥-elim (ln-left A≠B A∉AB)
       qed | inj₂ (inj₁ A∉CB) = A∉CB
       qed | inj₂ (inj₂ (inj₁ B∉AB)) = ⊥-elim (ln-right A≠B B∉AB)
       qed | inj₂ (inj₂ (inj₂ B∉CB)) = ⊥-elim (ln-right C≠B B∉CB)


```
-->




<!-- hidden

Las definiciones de setoid para Pt y Ln
```agda
  Pt♯ : Setoid♯ zero zero
  Pt♯ = record {
      _♯_ = DiPt ;
      isApartness = record { irreflexive = irref-DiPt ; cotransitivity = cotrans }
      }
      where  cotrans : {x y : Point} (z : Point) → DiPt x y → DiPt z x ⊎ DiPt z y
             cotrans z x≠y =
               case apartness-DiPt z x≠y of
                 \{ (inj₁ x≠z) → inj₁ (sym-DiPt x≠z)
                  ; (inj₂ y≠z) → inj₂ (sym-DiPt y≠z)
                  }




  Ln♯ : Setoid♯ zero zero
  Ln♯ = record {
      _♯_ = DiLn ;
      isApartness = record { irreflexive = irref-DiLn ; cotransitivity = cotrans }
      }
      where  cotrans : {x y : Line} (z : Line) → DiLn x y → DiLn z x ⊎ DiLn z y
             cotrans z x≠y =
               case apartness-DiLn z x≠y of
                 \{ (inj₁ x≠z) → inj₁ (sym-DiLn x≠z)
                  ; (inj₂ y≠z) → inj₂ (sym-DiLn y≠z)
                  }

  -- this setoid is not an instance
  Ln∦ : Setoid♯ zero zero
  Ln∦ = record {
      _♯_ = Con  ;
      isApartness = record { irreflexive = irref-Con
                           ; cotransitivity = λ z x∦y →
                                              case apartness-Con z x∦y of
                                              \{ (inj₁ x∦z) → inj₁ (sym-Con x∦z)
                                               ; (inj₂ y∦z) → inj₂ (sym-Con y∦z)
                                               }
                           }
      }

```
-->


<!-- hidden
# Some Abbreviations

## Traditional notation
```agda
  infix 4 _∉_
  infix 4 _∈_
  
  _∈_ _∉_ : Point → Line → Set
  _∈_ = Inc
  _∉_ = Apt

  -- alias for Con/Par
  _∥_ = Par
  _∦_ = Con
```


  
```agda
  open Setoid♯ ⦃...⦄
  instance
    _ = Ln♯
```
-->



<!--  Apartness Geometry Setoids and Lemmas
```agda
  -- Heyting/Mandelkern ∉
  _∀∈♯_ : Point → Line → Set
  P ∀∈♯ r = ∀{Q} → Q ∈ r → DiPt P  Q

  Apt→∀∈♯ : ∀ {P r} → Apt P r → P ∀∈♯ r
  Apt→∀∈♯ {P} {r} Apt-P-r {Q} Q∈r =
    case compat-Apt-EqPt P Q r Apt-P-r of
    \{ (inj₁ P♯Q) → P♯Q
     ; (inj₂ Apt-Q-r) → ⊥-elim (Q∈r Apt-Q-r)
     }




  --
  -- incidence and outside as Setoid binary relations
  --

  incidence : Rel♯ _ Pt♯ Ln♯
  incidence = record { ◇ = Inc ; isRel = record { sound = λ A≈B c≈d A∈c  → subs-Inc₁ (subs-Inc₂ A∈c c≈d) A≈B } } 

  outside : Rel♯ _ Pt♯ Ln♯
  outside = record { ◇ = Apt ; isRel = record { sound = λ A≈B c≈d A∉c  → subs-Apt₁ (subs-Apt₂ A∉c c≈d) A≈B } }

  DiPt♯ : Rel♯ _ Pt♯ Pt♯
  DiPt♯ = record { ◇ = DiPt ; isRel = isRel♯-♯ }

  DiLn♯ : Rel♯ _ Ln♯ Ln♯
  DiLn♯ = record { ◇ = DiLn ; isRel = isRel♯-♯ }

  -- not instance
  Rel♯-∦ : Rel♯ _ Ln∦ Ln∦
  Rel♯-∦ = record { ◇ = Con ; isRel = isRel♯-♯ }
  
  -- some useful lemmas --
  -- open Setoid♯ ⦃...⦄
  
 
  instance
    _ = Ln♯
    _ = Pt♯
    
  ∈∉→DiLn : ∀ {P r s} → P ∈ r → P ∉ s → r ♯ s
  ∈∉→DiLn {P} {r} {s} P∈r P∉s with compat-Apt-EqLn s r P P∉s
  ∈∉→DiLn {P} {r} {s} P∈r P∉s | inj₁ s♯r = symmetry s♯r
  ∈∉→DiLn {P} {r} {s} P∈r P∉s | inj₂ P∉r = ⊥-elim (P∈r P∉r)

  -- usual way to prove Apt
  ♯pt-∈→∉ :  ∀ {r s P} → (r∦s : Con r s)
                       → P ♯ pt r∦s
                       → P ∈ r
                       → P ∉ s
  ♯pt-∈→∉  r∦s P♯M P∈r
           with lemma-4-1-pt→ r∦s P♯M
  ... | inj₁ P∉r = ⊥-elim (P∈r P∉r)
  ... | inj₂ P∉s = P∉s


-- eq reasoning with points and lines
--

-- pt, ln commutativity
  ln-comm : ∀ {A B : Point}{A♯B : A ♯ B}{B♯A : B ♯ A} → ln A♯B ≈ ln B♯A
  ln-comm  = unq-ln _ (ln-right _) (ln-left _)
  pt-comm : ∀ {a b : Line}{a∦b : a ∦ b}{b∦a : b ∦ a} → pt a∦b ≈ pt b∦a
  pt-comm  = unq-pt _ (pt-right _) (pt-left _)

  -- proof irrelevant ln pt
  ln≈ : ∀ {A B : Point}{p₁ p₂ : A ♯ B} → ln p₁ ≈ ln p₂
  ln≈ = unq-ln _ (ln-left _) (ln-right _)
  pt≈ : ∀{a b : Line}{p₁ p₂ : a ∦ b} → pt p₁ ≈ pt p₂
  pt≈ = unq-pt _ (pt-left _) (pt-right _)


```
-->


# Projective Geometry




The projective geometry results by adding  the following axiom to the axioms of apartness geometry: 

*   All distinct lines are convergent.


```agda
record ProjectiveGeometry :  Set₁ where
  field
    AG :  ApartnessGeometry
  open ApartnessGeometry AG public 
  field
    DiLn→Con : ∀{r s} → DiLn r s → Con r s
  
  pt' : ∀ {l r} → (l♯r : DiLn l  r) → Point
  pt' = pt ∘ DiLn→Con

```

<!-- hidden 



# Affine Geometry

On the other hand, we define the record `AffineGeometry` as an extension
of `ApartnessGeometry` with:

-  a  method (`par`)to build a line parallel to a given line and passing by a given point.
-  an axiom `isPar-par`  which states that the constructed line is indeed parallel to the given line.
-  an axiom `isInc-par`  which states that the constructed line indeed pass by the given point. 
-  an axiom `uniqueness-parallel` which is the constructive version of the classical
   uniquenees axiom for parallel lines.


```agda
record AffineGeometry : Set₁ where
  field
    AG :  ApartnessGeometry
  open ApartnessGeometry AG public

  field

    -- construction of parallel lines
    par : Line → Point → Line

    -- soundness
    isPar-par : ∀ {l P} → Par l (par l P)
    isInc-par : ∀ {l P} → Inc P (par l P)

    -- uniqueness
    uniqueness-parallel
      : ∀ {l m} A → DiLn l m
        → Apt A l ⊎ Apt A m ⊎ Con l m
```

From `uniqueness-parallel`, we can infer the classical axiom:

* There exists a unique parallel to a given line passing by a given point.



```agda
  unq-par : ∀ {A l m} → Inc A l → Par l m → EqLn l (par m A)
```

<!-- prueba omitida
```agda
  unq-par {A} {l} {m } A∈l l∥m l♯par-mA =
    case uniqueness-parallel A  l♯par-mA of
    \{ (inj₁ A∉l) → A∈l A∉l
     ; (inj₂ (inj₁ A∉par-mA ) ) → isInc-par A∉par-mA
     ; (inj₂ (inj₂ l∦par-mA ) ) →
             case apartness-Con m l∦par-mA of
             \{ (inj₁ l∦m) → l∥m l∦m
              ; (inj₂ par-mA∦m) → isPar-par (sym-Con par-mA∦m)
              }
     }
```
-->


<!--
  
```agda
  open Setoid♯ ⦃...⦄
  instance
    _ = Ln♯
```
-->

<!-- 
## Lemmas and propositions for affine geometry
    
Distinct parallel lines have not common points.

```agda
  lemma-∥♯ :
    ∀ {l m : Line} A
    →  l ♯ m
    →  l ∥ m
    -----------
    →  A ∉ l
         ⊎
       A ∉ m
  lemma-∥♯  A l♯m l∥m
      with uniqueness-parallel A  l♯m
  lemma-∥♯ A l♯m l∥m | inj₁ A∉l = inj₁ A∉l
  lemma-∥♯ A l♯m l∥m | inj₂ (inj₁ A∉m) = inj₂ A∉m
  lemma-∥♯ A l♯m l∥m | inj₂ (inj₂ l∦m) = ⊥-elim (l∥m l∦m)
```

 --  variant of previous lemma 
```agda
  lemma-∥♯₁ :
       ∀ {l m A}
    →  l ♯ m
    →  l ∥ m
    →  A ∈ l
    -------------    
    →   A ∉ m
  lemma-∥♯₁ {A = A} l♯m l∥m A∈l
     with lemma-∥♯ A l♯m l∥m
  ... | inj₁ A∉l = ⊥-elim (A∈l A∉l)
  ... | inj₂ A∉m = A∉m
```


Parallel lines with a common point are equal.

```agda
  lemma-∥-common-point :
    ∀ {A l m}
    →  l ∥ m
    →  A ∈ l
    →  A ∈ m
    -----------
    → l ≈ m
  lemma-∥-common-point {A} {l} {m} l∥m A∈l A∈m =
    begin
      l          ≈⟨ unq-par A∈l refl ⟩
      par l A    ≈⟨ sym (unq-par A∈m (sym l∥m)) ⟩
      m
    ∎
    where open  import Relation.Binary.Reasoning.Setoid (Setoid♯.setoid Ln♯)
          instance
            _ = Ln∦
```

Distinc lines with a common point are convergent.

```agda
  lemma-♯-common-point→∦ :
    ∀  {A l m}
    →  l ♯ m
    →  A ∈ l
    →  A ∈ m
    ------------
    →  l ∦ m
  lemma-♯-common-point→∦ {A} l♯m A∈l A∈m
      with uniqueness-parallel A  l♯m
  lemma-♯-common-point→∦ {A} l♯m A∈l A∈m | inj₁       A∉l   = ⊥-elim (A∈l A∉l)
  lemma-♯-common-point→∦ {A} l♯m A∈l A∈m | inj₂ (inj₁ A∉m)  = ⊥-elim (A∈m A∉m)
  lemma-♯-common-point→∦ {A} l♯m A∈l A∈m | inj₂ (inj₂ l∦m)  = l∦m
```

--> 


## From Projective to Affine Geometry


```agda

module ProjectiveToAffine
       (Δ     :  ProjectiveGeometry        )
       (z     :  ProjectiveGeometry.Line Δ)

  where
```




```agda
  module 𝓟 = ProjectiveGeometry Δ
  instance
    _ = 𝓟.Ln♯
    _ = 𝓟.Pt♯
  -- improper line
  ln-∞ : 𝓟.Line        -- esto me parece que no va
  ln-∞ = z              --  
```


### Points and Lines


```agda
  Line : Set
  Line =  Σ[  r ∈ 𝓟.Line ] 𝓟.DiLn r z


  Point : Set
  Point = Σ[  P ∈ 𝓟.Point ] 𝓟.Apt P z
```


## Apartness Relations

The apartness relation for affine points and affine lines is inherited from the corresponding relations in 
the projective plane. 

```agda
  DiPt                  :   Point → Point  → Set
  DiPt (P , _) (Q , _)  =   𝓟.DiPt P Q

  DiLn                  :  Line → Line → Set
  DiLn (r , _) (s , _)  =  𝓟.DiLn r s
```

### Parallels and Convergent lines


```agda
  Con                  :  Line → Line → Set
  Con (r , _) (s , _)
      =  Σ[ r♯s ∈ 𝓟.DiLn r s ] 𝓟.Apt (𝓟.pt' r♯s) z  
```

The relation of *parallelism* is defined `a la von Plato` just as the negation of *convergence*.

```agda
  Par     :  Line → Line → Set
  Par r s = ¬ (Con r s)
```

## Outside Relation 

The definition of the *outside* relation for the reduced plane is just inherited from the
respective projective relation.

```agda
  Apt : Point → Line → Set
  Apt (P , _) (l , _) = 𝓟.Apt P l
```
  
## Line passing by two distinct points



```agda
  ln :  ∀{P Q : Point} → DiPt P Q → Line
  ln {(P , P∉z)} {Q} P♯Q
      = 𝓟.ln P♯Q                        -- the line PQ
        ,
        𝓟.∈∉→DiLn                      --  PQ ♯ z 
                (𝓟.ln-left P♯Q)             --  P ∈ PQ 
                P∉z                          --  P ∉ z

  pt : ∀{r s} → Con r s → Point
  pt  (r♯s , Q∉z)
      =  𝓟.pt' r♯s    -- the point Q = r ∩ s
         , 
         Q∉z            -- proof that Q ∈ z
```

### Lemmas about improper points


  
```agda
  _∞ : Line → 𝓟.Point
  (_ , r♯z) ∞ = 𝓟.pt' r♯z
```

We present two useful lemmas about improper points and parallel lines. 
The proof of this lemmas are ommited.


**Lemma:**  Convergent affine lines have different improper types

```agda
  lemma-∦→♯∞ : ∀   {a b : Line}
               →   Con a b
             -------------------
               →   𝓟.DiPt (a ∞)  (b ∞)
```
<!-- 

```agda
  lemma-∦→♯∞ {a , a♯z} {b , b♯z} (a♯b , Q∉z)=  𝓟.Apt→∀∈♯ A∉b (𝓟.pt-left (𝓟.DiLn→Con b♯z))
    where
      open Setoid♯ ⦃...⦄ 
      A B Q : 𝓟.Point
      A = 𝓟.pt' a♯z
      B = 𝓟.pt' b♯z
      Q = 𝓟.pt' a♯b
  
      Q♯A : 𝓟.DiPt Q  A
      Q♯A = 𝓟.Apt→∀∈♯ Q∉z (𝓟.pt-right (𝓟.DiLn→Con a♯z))
  
      Q♯B : 𝓟.DiPt Q  B
      Q♯B = 𝓟.Apt→∀∈♯ Q∉z (𝓟.pt-right (𝓟.DiLn→Con b♯z))
  
  
      A∉b : 𝓟.Apt A  b
      A∉b = 𝓟.♯pt-∈→∉ (𝓟.DiLn→Con a♯b) (symmetry Q♯A) (𝓟.pt-left (𝓟.DiLn→Con a♯z))
```
-->

And conversely:

**Lemma**: if the improper points of two lines are different, they are convergent
  

```agda
  lemma-♯∞→∦ : ∀  {a b}
             → 𝓟.DiPt (a ∞)  (b ∞)
             -------------
             → Con a b
```

<!--
```agda
  lemma-♯∞→∦ {a , a♯z} {b , b♯z} a∞♯b∞ = a♯b , Q∉z
     where
        open Setoid♯ ⦃...⦄   
        A B B' : 𝓟.Point
        A  = 𝓟.pt' a♯z
        B  = 𝓟.pt' b♯z
        B' = 𝓟.pt' $ symmetry b♯z
        B≈B' : B ≈ B'
        B≈B' = 𝓟.pt-comm
  
        open Rel♯ 𝓟.DiPt♯
  
        A∉b : 𝓟.pt' a♯z  𝓟.∉ b
        A∉b =  𝓟.♯pt-∈→∉ (𝓟.DiLn→Con (symmetry b♯z)) (a∞♯b∞ ⇒⟨ B≈B' ⟩) (𝓟.pt-right (𝓟.DiLn→Con a♯z))
  
        a♯b : a ♯ b
        a♯b = 𝓟.∈∉→DiLn (𝓟.pt-left _) A∉b
  
        Q : 𝓟.Point
        Q = 𝓟.pt' a♯b
  
        A♯Q : A ♯ Q
        A♯Q = 𝓟.Apt→∀∈♯ A∉b (𝓟.pt-right _)
  
        Q∉z : Q 𝓟.∉ z
        Q∉z = 𝓟.♯pt-∈→∉ (𝓟.DiLn→Con a♯z) (symmetry A♯Q) (𝓟.pt-left _)
```

  
As a corollary, we conclude that parallel lines have the same improper point and conversely.

```agda
  lemma-∥→≈∞ : ∀  {a b}
               →  Par a b
               ------------
               → 𝓟.EqPt (a ∞)  (b ∞)
  lemma-∥→≈∞ a∥b = λ a∞♯b∞ → a∥b (lemma-♯∞→∦ a∞♯b∞)
  
  lemma-≈∞→∥ : ∀{a b} → 𝓟.EqPt (a ∞)  (b ∞) → Par a b
  lemma-≈∞→∥ a∞≈b∞ = λ a∦b → a∞≈b∞ (lemma-∦→♯∞ a∦b)
```

-->


### Cotransitivity of the Basic Relations


```agda
  apartness-DiPt : ∀  {a b} c
                   → DiPt a b
                   → DiPt a c ⊎ DiPt b c
  apartness-DiPt = 𝓟.apartness-DiPt ∘ proj₁
                 
  apartness-DiLn : ∀  {a b} c
                   → DiLn a b
                   → DiLn a c ⊎ DiLn b c
  apartness-DiLn = 𝓟.apartness-DiLn ∘ proj₁ 


  apartness-Con : ∀ {a b} c → Con a b → Con a c ⊎ Con b c
  apartness-Con {a} {b}  c  a∦b
     = proof-of-apartness-Con  -- defined bellow
            where
              A  B C : 𝓟.Point
              A = a ∞  
              B = b ∞
              C = c ∞
              A♯B : 𝓟.DiPt A B
              A♯B = lemma-∦→♯∞ a∦b

              proof-of-apartness-Con : Con a c ⊎ Con b c
              proof-of-apartness-Con
                   with 𝓟.apartness-DiPt C A♯B
              ... | inj₁ A♯C = inj₁ (lemma-♯∞→∦ A♯C)  -- α ∦ c
              ... | inj₂ B♯C = inj₂ (lemma-♯∞→∦ B♯C)  -- b ∦ c
```

### Uniqueness Axiom for the Reduced Plane


```agda
  uniqueness :  {A B : Point} {l m : Line}
               → DiPt A B → DiLn l m
               → Apt A l ⊎ Apt A m ⊎ Apt B l ⊎ Apt B m
  uniqueness A♯B l♯m =  𝓟.uniqueness A♯B l♯m
```

### Compatibility with equality


```agda
  compat-Con-EqLn :
      ∀   (l m n : Line)
      →  Con l m
      ----------------------
      →  DiLn m n ⊎ Con l n

  compat-Con-EqLn l m n@(n' , _)  l∦m@(l♯m , M∉z)
      with 𝓟.compat-Con-EqLn _ _ n' (𝓟.DiLn→Con l♯m)
  ... | inj₁ m♯n = inj₁ m♯n
  ... | inj₂ l∦n =  m♯n-∨-l∦n
        where M = 𝓟.pt' l♯m
              open Setoid♯ ⦃...⦄ 
              L = l ∞
  
              M♯L : M ♯ L
              M♯L = 𝓟.Apt→∀∈♯ M∉z (𝓟.pt-right _)
  
              Q = 𝓟.pt l∦n
  
              open Rel♯ 𝓟.DiPt♯
  
              m♯n-∨-l∦n : DiLn m n ⊎ Con l n
              m♯n-∨-l∦n with cotransitivity Q M♯L
              m♯n-∨-l∦n | inj₁ Q♯M = inj₁ (symmetry (𝓟.∈∉→DiLn (𝓟.pt-right l∦n) (𝓟.♯pt-∈→∉ (𝓟.DiLn→Con l♯m) Q♯M (𝓟.pt-left _))))
              m♯n-∨-l∦n | inj₂ Q♯L = inj₂ ((𝓟.Con→DiLn l∦n) , (𝓟.♯pt-∈→∉ (𝓟.DiLn→Con $ proj₂ l) (⟨ 𝓟.pt≈ ⟩⇐ Q♯L) (𝓟.pt-left _)))
```


### The Apartness Geometry Structure


```agda
  apartness : ApartnessGeometry
  apartness =
    record {
      Point = Point;
      Line  = Line;
      
      DiPt = DiPt ;
      DiLn = DiLn ;
      Con = Con ;
      Apt =  Apt ;
      ln =  λ {A} {B} → ln {A} {B};
      pt = λ {x} {y} → pt {x} {y}  ;
      irref-DiPt = 𝓟.irref-DiPt ;
      irref-DiLn = 𝓟.irref-DiLn ;
      irref-Con = 𝓟.irref-Con ∘ 𝓟.DiLn→Con ∘ proj₁  ;
      apartness-DiPt
        =  λ {A} {B} C → apartness-DiPt {A} {B} C ;
      apartness-DiLn
        =  λ {a} {b} c → apartness-DiLn {a} {b} c;
      apartness-Con
        = λ {a} {b} c → apartness-Con {a} {b} c ;
      ln-left  = 𝓟.ln-left ; 
      ln-right = 𝓟.ln-right ;
      pt-left
        = 𝓟.pt-left ∘ 𝓟.DiLn→Con ∘ proj₁ ;
      pt-right
          = 𝓟.pt-right ∘ 𝓟.DiLn→Con ∘ proj₁ ;
      uniqueness = 𝓟.uniqueness ;
      compat-Apt-EqPt = λ _ _ _ → 𝓟.compat-Apt-EqPt _ _ _ ;
      compat-Apt-EqLn = λ _ _ _ → 𝓟.compat-Apt-EqLn _ _ _ ;
      compat-Con-EqLn = compat-Con-EqLn
      }
```


<!--
```agda
  open ApartnessGeometry apartness
    using (Inc)
```
-->

### The parallel construction

```agda
  par : Line → Point → Line
  par (l , l♯z) (P , P∉z)
     =  𝓟.ln P♯L ,  𝓟.∈∉→DiLn (𝓟.ln-left _) P∉z
    where
      open Setoid♯ ⦃...⦄ 
      L : 𝓟.Point
      L = 𝓟.pt' l♯z
  
      P♯L : P ♯ L
      P♯L = 𝓟.Apt→∀∈♯ P∉z (𝓟.pt-right _) 

  isPar-par : {l : Line} → {P : Point} → Par l (par l P)
  isPar-par {l} {P}
            (l♯l' , Q∉z) -- asumption
            = L∈z                      -- L∈z
              (𝓟.subs-Apt₁ Q∉z Q≈L)   -- L∉z
    where
      Q L : 𝓟.Point
      Q   = 𝓟.pt' l♯l'
      L   = l ∞
  
      Q≈L : 𝓟.EqPt Q L
      Q≈L
         = 𝓟.sym-EqPt (𝓟.unq-pt _ (𝓟.pt-left _) (𝓟.ln-right _))
  
      L∈z : L 𝓟.∈ z
      L∈z = 𝓟.pt-right _

  isInc-par : ∀ {l P} → Inc P (par l P)
  isInc-par   = 𝓟.ln-left _
```

### Uniqueness axiom for parallels


```agda
  uniqueness-parallel :
        ∀   {l m} A
        →  DiLn l m
        -------------------------------
        →  Apt A l ⊎ Apt A m ⊎ Con l m

  uniqueness-parallel  {l} {m} AA@(A , A∉z) l♯m = goal
    where
      L Q : 𝓟.Point
      L = l ∞
      Q = 𝓟.pt' l♯m

      A♯L : 𝓟.DiPt A  L
      A♯L = 𝓟.Apt→∀∈♯ A∉z (𝓟.pt-right _)

      goal : Apt AA l ⊎ Apt AA m ⊎ Con l m
      goal with  𝓟.apartness-DiPt  Q A♯L
      goal | inj₁ A♯Q
           with 𝓟.lemma-4-1-pt→  (𝓟.DiLn→Con l♯m) A♯Q
      goal | inj₁ A♯Q | inj₁ A∉l     =   inj₁ A∉l   
      goal | inj₁ A♯Q | (inj₂ A∉m)   =   inj₂ (inj₁ A∉m)

      goal | inj₂ L♯Q
        = inj₂ (inj₂ (
           l♯m ,
           (𝓟.♯pt-∈→∉ _ (𝓟.sym-DiPt L♯Q)  (𝓟.pt-left _)))
           )
```


### The Affine Geometry Structure


```agda
  affine :  AffineGeometry
  affine = record
   { AG = apartness
   ; par = par
   ; isPar-par =  isPar-par
   ; isInc-par = isInc-par
   ; uniqueness-parallel
      = λ {l} {m} → uniqueness-parallel {l} {m}
   }
```

