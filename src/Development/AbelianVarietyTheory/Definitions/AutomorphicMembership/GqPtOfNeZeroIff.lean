module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MulVecMemLatMap
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Matrix.Diagonal
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

-- Source module: Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DiagMemCongruencePairs

section

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob

variable {E : Type} [Field E] [NumberField E]

abbrev Lz (E : Type) [Field E] (m : ℕ) : Type := Submodule (𝓞 E) (Fin m → E) × (Fin m → E)

def zOf {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Fin n → E := fun i => P i (Fin.last r)

def spanX {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Submodule E (Fin n → E) :=
  LinearMap.range (eOf P).mulVecLin

def perpX (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E) :
    Submodule E (Fin n → E) := LinearMap.ker (cT σ (eOf P) * J).mulVecLin

def latIn {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (S : Submodule E (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) := Λ ⊓ S.restrictScalars (𝓞 E)

def mulLat {n : ℕ} (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  Λ.map ((g : 𝓞 E) • LinearMap.id)

def IsRed (σ : E →+* E) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Jb : Matrix (Fin m) (Fin m) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) (x : Lz E m)
    (al : Matrix (Fin m) (Fin n) E) : Prop :=
  (∀ v ∈ perpX σ J P, al *ᵥ v = 0 ↔ v ∈ spanX P) ∧
  (∀ y, ∃ v ∈ perpX σ J P, al *ᵥ v = y) ∧
  (∀ v ∈ perpX σ J P, ∀ w ∈ perpX σ J P, form σ Jb (al *ᵥ v) (al *ᵥ w) = form σ J v w) ∧
  (latIn Λ (perpX σ J P)).map (al.mulVecLin.restrictScalars (𝓞 E)) = x.1 ∧
  al *ᵥ zOf P = x.2

def UO (E : Type) [Field E] [NumberField E] (r : ℕ) : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E) :=
  {u | IsUp u ∧ ∀ a b : Fin (r + 1), a < b → u a b ∈ dInv E ((b : ℕ) - a)}

section Basic

variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}



omit [NumberField E] in
theorem mem_perpX (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ perpX σ J P ↔ (cT σ (eOf P) * J) *ᵥ v = 0 := Iff.rfl


omit [NumberField E] in
theorem mem_perpX_iff_form (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ perpX σ J P ↔ ∀ a : Fin r, form σ J v (fun i => P i a.castSucc) = 0 := by
  rw [mem_perpX, ← Matrix.mulVec_mulVec, funext_iff]
  rfl




omit [NumberField E] in
theorem mem_latMap (γ : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E) :
    v ∈ latMap γ Λ ↔ ∃ w ∈ Λ, γ *ᵥ w = v := Iff.rfl









end Basic

section Iota

variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}

end Iota

section Iso

variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}



omit [NumberField E] in
theorem isUn_mul {γ δ : Matrix (Fin n) (Fin n) E} (hγ : IsUn σ J γ) (hδ : IsUn σ J δ) :
    IsUn σ J (γ * δ) := by
  have e : cT σ (γ * δ) = cT σ δ * cT σ γ := by rw [cT, Matrix.map_mul, Matrix.transpose_mul]; rfl
  rw [IsUn, e, show cT σ δ * cT σ γ * J * (γ * δ) = cT σ δ * (cT σ γ * J * γ) * δ by
    simp only [Matrix.mul_assoc], hγ, hδ]


theorem latMap_one (Λ : Submodule (𝓞 E) (Fin n → E)) : latMap 1 Λ = Λ := by
  ext v
  simp [mem_latMap]

theorem latMap_mul (γ δ : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    latMap (γ * δ) Λ = latMap γ (latMap δ Λ) := by
  rw [latMap, latMap, latMap, ← Submodule.map_comp, Matrix.mulVecLin_mul]
  rfl

end Iso

section Unip

variable {n r : ℕ}

end Unip

section Examples

variable {σ : E →+* E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

end Examples

end GlobalTheory.SgGlob
end
end
end

-- Source module: Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMassConst

section

@[expose] public section

noncomputable section
open ValuativeRel IsDedekindDomain NumberField ComplexConjugate Formalism.MainNotions.S.Loc Matrix MeasureTheory
open scoped Classical

namespace GlobalTheory.SgGlob

section Rat
variable {E : Type} [Field E] [NumberField E]

def eps (K : Type) [CommRing K] (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.diagonal fun b => (-1) ^ (r - (b : ℕ))

end Rat

namespace ModFam
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {g₁ g₂ : ℕ} (X : ModFam F E sig g₁ g₂)

end ModFam

end GlobalTheory.SgGlob
end
end
end

-- Source module: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PrimInIffSubsingleton

section

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

section Defs

def LieN (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (Y : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  cT σ Y * J + J * Y = 0 ∧ IsStrict A ∧ Y * P = P * A ∧ ∀ x ∈ perpX σ J P, Y *ᵥ x ∈ spanX P

def Relevant (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∀ Y A A', LieN σ J P Y A → LieN σ J P' Y A' →
    (simpleSum A - simpleSum A') + σ (simpleSum A - simpleSum A') = 0

def LiesAt {r : ℕ} (w : Formalism.MainNotions.S.Point E (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  ∃ l u : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsLo l ∧ IsUp u ∧ Z * eps E r = l * Formalism.MainNotions.S.ptMat w * u

def onePt (E : Type) [Field E] (r : ℕ) : Formalism.MainNotions.S.Point E (r + 1) := ⟨[(1, r + 1)], by simp, by simp⟩


variable [NumberField E]

def IntFrame (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T : E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  IsFrame σ J T P ∧ PrimIn (frameLat P) Λ

def Cong {n r : ℕ} (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  frameLat ((g : E)⁻¹ • (P' - P)) ≤ Λ

def admitted (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T' : E) (g : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  IntFrame σ J T' Λ P' ∧ ∃ u ∈ UO E r, Cong g Λ (P * u) P'

def NO (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Set (Matrix (Fin n) (Fin n) E) :=
  {s | InN σ J P s ∧ latMap s Λ = Λ}

def Move (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P A B : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∃ s ∈ NO σ J Λ P, ∃ u ∈ UO E r, B = s * A * u

end Defs

section Field

variable {σ : E →+* E} {n r : ℕ} {J s Y : Matrix (Fin n) (Fin n) E} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
  {u v A Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E}

end Field

section Lattice

variable [NumberField E] {σ : E →+* E} {n r g : ℕ} {J s : Matrix (Fin n) (Fin n) E}
  {P P' A B C : Matrix (Fin n) (Fin (r + 1)) E} {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  {Λ Λ' Λ'' M : Submodule (𝓞 E) (Fin n → E)} {T T' : E}

end Lattice

end GlobalTheory.IntTerm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GqPtOfNeZeroIff

section

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

section Defs

variable {E : Type} [Field E] [NumberField E] (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)

def Col (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Quot fun Λ Λ' : FrameLats σ J P => ∃ s, InS σ J P s ∧ latMap s Λ.1 = Λ'.1

def Col.lat {σ : E →+* E} {J : Matrix (Fin n) (Fin n) E} {P : Matrix (Fin n) (Fin (r + 1)) E} (c : Col σ J P) :
    Submodule (𝓞 E) (Fin n → E) := (Quot.out c).1

def FrCls (T' : E) (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Quot fun A B : {A // admitted σ J T' g Λ P A} => Move σ J Λ P A.1 B.1

def Term (T' : E) (g : ℕ) (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Σ c : Col σ J P, FrCls σ J T' g c.lat P



variable {σ J} {T' : E} {g : ℕ} {P : Matrix (Fin n) (Fin (r + 1)) E}

namespace Term

variable (t : Term σ J T' g P)

end Term

end Defs

section Basic

variable {E : Type} [Field E] [NumberField E] {σ : E →+* E} {n r g : ℕ} {J : Matrix (Fin n) (Fin n) E}
  {T T' : E} {P A B : Matrix (Fin n) (Fin (r + 1)) E} {Λ : Submodule (𝓞 E) (Fin n → E)}






namespace Term

variable (t : Term σ J T' g P)

variable {t}

variable (t)

end Term

end Basic

section Examples

variable {E : Type} [Field E] [NumberField E]

end Examples

section Spaces

open Formalism.BasicNotions

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def coMat (V : HSpace E) {a : Type} (x : a → V.V) : Matrix (Fin V.rank) a E :=
  Matrix.of fun i b => V.frame.repr (x b) i

theorem hT_eq_sum (V : HSpace E) (x y : V.V) :
    V.hT x y = ∑ j, (∑ i, star (V.frame.repr x i) * V.gram i j) * V.frame.repr y j := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]

  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
  RingHom.id_apply, HSpace.gram, starRingEnd_apply, mul_comm]

end Spaces

section Record

open Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

variable {D} {u u' : D.what₂.Word}

end Record

end GlobalTheory.IntTerm
end
end
end
