module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleDetTwistOfStdTraceTwoBlockStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleHarishChandraOfStdTraceNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsConstituentOfRepIsoLeft
public import Mathlib.RepresentationTheory.Character
import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbittAlg
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLabelRootOfHarishChandraConstituentStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassFunctionLabelOfLabelMapLabelStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConstituentHarishChandraRepIffPairingNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterIffIsCuspidalGLnFiniteFieldStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterOfPolynomialOfCuspidalLabelStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceHarishChandraInducedEqProductCharactersStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardTypeVectorOfParabolicTypeVector

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LevelType
open Matrix

theorem exists_stdVec_of_parVec : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ Fin r) (a : α) (θ : (ZMod p)ˣ →* ℂˣ) (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL (Fin r) (ZMod p)) U) (v : U), Fintype.card (m a) = 1 → v ≠ 0 → ParVec ρ e a θ v → ∃ (c : ℕ) (v' : U), c < r ∧ v' ≠ 0 ∧ StdVec ρ c θ v' := by
  intro p _ r α _ _ m _ _ e a θ U _ _ ρ v hm hv hpar
  obtain ⟨k0⟩ : Nonempty (m a) := Fintype.card_pos_iff.1 (by omega)
  let σ := Tuple.sort (blk e)
  let i₀ := e ⟨a, k0⟩
  have hi₀ : blk e i₀ = a := blk_apply e a k0
  have hmono := Tuple.monotone_sort (blk e)
  have hlt : ∀ i, blk e i < a → σ.symm i < σ.symm i₀ := fun i h => hmono.reflect_lt (by
    show blk e (σ (σ.symm i)) < blk e (σ (σ.symm i₀))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hi₀]; exact h)
  have hgt : ∀ i, a < blk e i → σ.symm i₀ < σ.symm i := fun i h => hmono.reflect_lt (by
    show blk e (σ (σ.symm i₀)) < blk e (σ (σ.symm i))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hi₀]; exact h)
  have hlo : ∀ i, (σ.symm i).val ≤ (σ.symm i₀).val → blk e i ≤ a := fun i h => by
    by_contra h'
    exact absurd h (not_le.2 (Fin.lt_def.1 (hgt i (not_le.1 h'))))
  have hhi : ∀ j, (σ.symm i₀).val ≤ (σ.symm j).val → a ≤ blk e j := fun j h => by
    by_contra h'
    exact absurd h (not_le.2 (Fin.lt_def.1 (hlt j (not_le.1 h'))))
  refine ⟨(σ.symm i₀).val, ρ (GlobalTheory.Parabolic.permGL (ZMod p) σ.symm) v, (σ.symm i₀).isLt, ?_, ?_⟩
  · intro h0
    apply hv
    have := congrArg (ρ (GlobalTheory.Parabolic.permGL (ZMod p) σ.symm)⁻¹) h0
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] at this
  · intro x hx
    set y := (GlobalTheory.Parabolic.permGL (ZMod p) σ.symm)⁻¹ * x * GlobalTheory.Parabolic.permGL (ZMod p) σ.symm with hy
    have hyij : ∀ i j, ¬ (blk e i ≤ a ∧ a ≤ blk e j) → y.val i j = if i = j then 1 else 0 := by
      intro i j hij
      have hyv : y.val i j = x.val (σ.symm i) (σ.symm j) := by
        rw [← GlobalTheory.Parabolic.conj_permGL_apply σ.symm y i j, hy]
        congr 2
        group
      rw [hyv, hx _ _ (fun h => hij ⟨hlo i h.1, hhi j h.2⟩)]
      simp
    have hyP : y ∈ parab (ZMod p) e := mem_parab.2 fun i j hji => by
      rw [hyij i j (fun h => absurd (h.1.trans h.2) (not_le.2 hji)), if_neg]
      rintro rfl
      exact lt_irrefl _ hji
    have hlev : ∀ b, b ≠ a → leviProj (ZMod p) e ⟨y, hyP⟩ b = 1 := by
      intro b hb
      refine Units.ext (Matrix.ext fun k l => ?_)
      rw [leviProj_apply, Units.val_one]
      rw [hyij _ _ (fun h => hb (le_antisymm (by simpa using h.1) (by simpa using h.2)))]
      simp [Matrix.one_apply]
    have h1 := hpar ⟨y, hyP⟩ hlev
    change ρ y v = (θ (GeneralLinearGroup.det y) : ℂ) • v at h1
    have hdet : GeneralLinearGroup.det y = GeneralLinearGroup.det x := by
      rw [hy, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
    have hxP : x * GlobalTheory.Parabolic.permGL (ZMod p) σ.symm = GlobalTheory.Parabolic.permGL (ZMod p) σ.symm * y := by rw [hy]; group
    rw [← Module.End.mul_apply, ← map_mul, hxP, map_mul, Module.End.mul_apply, h1, hdet, map_smul]

end GlobalTheory.LevelType
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardTypeVectorOfParabolicTypeVectorStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_standardTypeVector_of_parabolicTypeVector : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ Fin r) (a : α) (θ : (ZMod p)ˣ →* ℂˣ) (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL (Fin r) (ZMod p)) U) (v : U), Fintype.card (m a) = 1 → v ≠ 0 → ParVec ρ e a θ v → ∃ (c : ℕ) (v' : U), c < r ∧ v' ≠ 0 ∧ StdVec ρ c θ v' := by
  first | exact @GlobalTheory.LevelType.exists_stdVec_of_parVec | exact GlobalTheory.LevelType.exists_stdVec_of_parVec | (intros; apply GlobalTheory.LevelType.exists_stdVec_of_parVec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdParabolicTwistedTraceSumNeZeroOfVector

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LevelType

theorem StdBlock.mul {p r : ℕ} {a : ℕ} {x y : GL (Fin r) (ZMod p)} (hx : StdBlock a x) (hy : StdBlock a y) :
    StdBlock a (x * y) := by
  intro i j hij
  rw [Units.val_mul, Matrix.mul_apply]
  by_cases hi : i.val ≤ a
  · have hj : ¬ a ≤ j.val := fun h => hij ⟨hi, h⟩
    have : ∀ k, y.val k j = if k = j then 1 else 0 := fun k => hy k j (fun h => hj h.2)
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hx i j hij
  · have : ∀ k, x.val i k = if i = k then 1 else 0 := fun k => hx i k (fun h => hi h.1)
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hy i j hij

theorem stdBlock_one {p r : ℕ} (a : ℕ) : StdBlock a (1 : GL (Fin r) (ZMod p)) := by
  intro i j _
  simp [Matrix.one_apply]

theorem stdTrace_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (r a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (v : ρ), v ≠ 0 → StdVec ρ.ρ a θ v → stdTrace a θ ρ.character ≠ 0 := by
  intro p _ r a θ ρ v hv0 hv
  classical
  set S : Finset (GL (Fin r) (ZMod p)) := Finset.univ.filter (StdBlock a) with hS
  set c : GL (Fin r) (ZMod p) → ℂ := fun x => (((θ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) with hc
  have hcm : ∀ x y, c (x * y) = c x * c y := fun x y => by
    simp [hc, map_mul, mul_inv, Units.val_mul, mul_comm]
  set E : Module.End ℂ ρ := ∑ x ∈ S, c x • ρ.ρ x with hE
  have htr : stdTrace a θ ρ.character = LinearMap.trace ℂ ρ E := by

    rw [hE, map_sum, stdTrace, hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp [FDRep.character, hc]
  have himg : ∀ x ∈ S, S.image (x * ·) = S := fun x hx => by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
      exact hx.mul hy
    · rw [Finset.card_image_of_injective _ (mul_right_injective x)]
  have hEE : E * E = (S.card : ℂ) • E := by
    have : ∀ x ∈ S, (c x • ρ.ρ x) * E = E := fun x hx => by
      rw [hE, Finset.mul_sum]
      conv_rhs => rw [← himg x hx]
      rw [Finset.sum_image (fun y _ z _ h => mul_left_cancel h)]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [smul_mul_smul_comm, ← map_mul, hcm x y]
    calc E * E = ∑ x ∈ S, (c x • ρ.ρ x) * E := by rw [hE, Finset.sum_mul]
      _ = ∑ x ∈ S, E := Finset.sum_congr rfl this
      _ = (S.card : ℂ) • E := by rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have hEv : E v = (S.card : ℂ) • v := by
    rw [hE, LinearMap.sum_apply, Finset.sum_congr rfl (g := fun _ => v), Finset.sum_const, Nat.cast_smul_eq_nsmul]
    intro x hx
    rw [LinearMap.smul_apply, hv x (by simpa [hS] using hx), smul_smul]
    simp [hc]
  have hcard : (S.card : ℂ) ≠ 0 := by
    have : (1 : GL (Fin r) (ZMod p)) ∈ S := by simpa [hS] using stdBlock_one (p := p) (r := r) a
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem this)
  set P : Module.End ℂ ρ := (S.card : ℂ)⁻¹ • E with hP
  have hPP : IsIdempotentElem P := by
    rw [IsIdempotentElem, hP, smul_mul_smul_comm, hEE, smul_smul]
    congr 1
    field_simp
  have hPv : P v = v := by
    rw [hP, LinearMap.smul_apply, hEv, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hP0 : P ≠ 0 := fun h => hv0 (by rw [← hPv, h, LinearMap.zero_apply])
  have htP : LinearMap.trace ℂ ρ P ≠ 0 := fun h => hP0 ((LinearMap.IsIdempotentElem.trace_eq_zero_iff hPP).1 h)
  rw [htr]
  have : E = (S.card : ℂ) • P := by rw [hP, smul_smul, mul_inv_cancel₀ hcard, one_smul]
  rw [this, map_smul, smul_eq_mul]
  exact mul_ne_zero hcard htP

end GlobalTheory.LevelType

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdParabolicTwistedTraceSumNeZeroOfVectorStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.stdParabolicTwistedTraceSum_ne_zero_of_vector : ∀ (p : ℕ) [Fact p.Prime] (r a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (v : ρ), v ≠ 0 → StdVec ρ.ρ a θ v → stdTrace a θ ρ.character ≠ 0 := by
  first | exact @GlobalTheory.LevelType.stdTrace_ne_zero | exact GlobalTheory.LevelType.stdTrace_ne_zero | (intros; apply GlobalTheory.LevelType.stdTrace_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitLocalOfGreen

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockTypeSplit

open ValuativeRel Polynomial

section Finite

theorem isRoot_of_parVec {p : ℕ} [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) {r : ℕ} {α : Type} [Fintype α] [LinearOrder α]
    {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ Fin r) (a : α)
    {θ : (ZMod p)ˣ →* ℂˣ} {u : ZMod p} {f : (ZMod p)[X]} (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (hρ : CategoryTheory.Simple ρ)
    (hf : GlobalTheory.GLq.HasLabel L (fun x => ρ.character x) f) (hθ : GlobalTheory.GLp.IsCharLab L θ u) (ha : Fintype.card (m a) = 1)
    {v : ρ} (hv : v ≠ 0) (h : ParVec ρ.ρ e a θ v) : f.IsRoot u := by
  obtain ⟨c, v', hc, hv', hs⟩ := GlobalTheory.T.exists_standardTypeVector_of_parabolicTypeVector p r α m e a θ _ ρ.ρ v ha hv h
  have ht := GlobalTheory.T.stdParabolicTwistedTraceSum_ne_zero_of_vector p r c θ ρ v' hv' hs
  have hr : r = c + 1 + (r - c - 1) := by omega
  obtain ⟨A, B, hA, hB, h1, h2⟩ := GlobalTheory.T.exists_irreducible_harishChandra_of_stdTrace_ne_zero p r c (r - c - 1) θ ρ.character hr ⟨ρ, fun _ => rfl⟩ ht
  obtain ⟨σ, hσ, h3⟩ := GlobalTheory.T.exists_irreducible_detTwist_of_stdTrace_twoBlock p c θ A hA h2
  exact GlobalTheory.T.thetaLabel_root_of_harishChandraConstituent p L r c _ θ u f _ A B σ hr ⟨ρ, hρ, fun _ => rfl⟩ hA hB hσ hf hθ h1 h3

end Finite

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem isSubquotient_jac_two {a b n V W : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n]
    [DecidableEq n] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : a ⊕ b ≃ n)
    {π : Representation ℂ (GL n F) V} {τ : Representation ℂ (GL n F) W} (hτ : IsSmooth τ) (h : IsSubquotient π τ) :
    IsSubquotient (jac (two e) π) (jac (two e) τ) := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap τ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  refine (IsSubquotient.of_surjective (jacMap (two e) f) fun y => ?_).trans (.of_injective (jacMap (two e) ι) ?_)
  · obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨v, rfl⟩ := hf w
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : ι v ∈ twKer τ (unipRad F (two e)) 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
    have hN := GlobalTheory.InertSupp.unipRad_eq_unipOf F (e := two e) (c := fun i => ((blk (two e) i).toNat : ℤ))
      fun i j => by cases blk (two e) i <;> cases blk (two e) j <;> simp
    obtain ⟨T, hT, h2⟩ := GlobalTheory.JacquetExact.exists_finset_of_mem_twKer h1
    obtain ⟨H, hle, hH, hSH⟩ := GlobalTheory.UnipCompact.exists_compact_subgroup F n _ T (hN ▸ hT)
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    exact GlobalTheory.IwahoriInj.twKer_mono (hle.trans hN.ge)
      (GlobalTheory.JacquetExact.mem_twKer_of_compact hτ ι Subtype.val_injective hH (h2 H hSH))

variable {p : ℕ} [Fact p.Prime] {r t : ℕ}

theorem typeVec_first {X : Bool → Type} [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)]
    (ρ : ∀ j, Representation ℂ (GL (Two (Fin r) (Fin t) j) F) (X j)) (hρ : ∀ j, IsSmooth (ρ j))
    {Y : Type} [AddCommGroup Y] [Module ℂ Y] {τ : Representation ℂ (Levi F (Two (Fin r) (Fin t))) Y}
    (h : IsSubquotient τ (piTensor ρ)) {z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))} {w : Y}
    (hw : TypeVec (n := Fin r) (τ.comp (MonoidHom.mulSingle (fun j => GL (Two (Fin r) (Fin t) j) F) false)) z w) :
    ∃ x, TypeVec (n := Fin r) (ρ false) z x := by
  obtain ⟨y, hy⟩ := TypeVec.up (n := Fin r)
    (π := (piTensor ρ).comp (MonoidHom.mulSingle (fun j => GL (Two (Fin r) (Fin t) j) F) false))
    (isSmooth_comp (isSmooth_piTensor hρ) _ (continuous_mulSingle (A := fun j => GL (Two (Fin r) (Fin t) j) F) false))
    (GlobalTheory.CuspRep.ParLaws.isSubquotient_comp h _) hw
  exact TypeVec.factor (m := Two (Fin r) (Fin t)) ρ false hy

theorem typeVec_iff {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin r) F) W)
    (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (y : W) (h : TypeVec π z y) : IsLevelOne π y ∧ NotKilled π z y := by
  obtain ⟨h1, ℓ, hℓ, h0⟩ := h
  refine ⟨fun h hh => h1 h (GlobalTheory.StepData.mem_KOne.2 fun a b => ?_), ℓ, fun g a b => ?_, h0⟩
  · simpa [Matrix.one_apply] using hh a b
  · rw [dite_eq_left ⟨a.2, b.2⟩]
    exact hℓ g a b

end Local

theorem hasLabelO_of_mul {p : ℕ} [Fact p.Prime] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod p)}
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod p) C) {r : ℕ} (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (hρ : CategoryTheory.Simple ρ)
    {f : (ZMod p)[X]} (h0 : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ ≠ 0)
    (h : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * Formalism.L2.NT.eSerO O r f = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) : Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O ρ f := by
  classical
  rw [GlobalTheory.SerOSys.eSerO_eq_sum, Finset.mul_sum] at h
  obtain ⟨z, hz, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h.trans_ne h0)
  obtain ⟨τ, hτ, rfl, hl⟩ := (GlobalTheory.SerOSys.Zl_finite O r f).mem_toFinset.1 hz
  refine GlobalTheory.SerOSys.hasLabelO_of_repIso O hl (GlobalTheory.SerOSys.repIso_of_zIdem_eq ρ τ hρ hτ ?_)
  by_contra e
  exact hne (GlobalTheory.SerOSys.zIdem_mul_eq_zero ρ τ hρ hτ e)

theorem exists_hasLabel {p : ℕ} [Fact p.Prime] (t : Formalism.CyclotomicNorms.Fbar p →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar p, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar p) (hζ : Formalism.L2.NT.IsGenSys ζ)
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod p) (Formalism.L2.NT.convC t ht ζ hζ))
    (hO : ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod p))), 1 ≤ d → CategoryTheory.Simple τ →
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod p) τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (Formalism.L2.NT.convC t ht ζ hζ) τ (O.lab d τ))
    {r : ℕ} (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (hρ : CategoryTheory.Simple ρ) {f : (ZMod p)[X]}
    (h0 : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ ≠ 0)
    (h : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * Formalism.L2.NT.eSerO O r f = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) :
    ∃ L : GlobalTheory.GLq.LabelDatum p, L.teich = t ∧ L.gen = ζ ∧ GlobalTheory.GLq.HasLabel L (fun x => ρ.character x) f := by
  let L : GlobalTheory.GLq.LabelDatum p := ⟨t, ht, ζ, fun d hd => (hζ d hd).1,
    fun d e hd he => (hζ d hd).2 (d * e) (dvd_mul_right d e) (Nat.mul_pos hd he)⟩
  exact ⟨L, rfl, rfl, GlobalTheory.T.classFunctionLabel_of_labelMap_label p L O (fun d V hd hs hc => GlobalTheory.T.isCuspidalCharacterOfPolynomial_of_cuspidalLabel p L t ht hζ rfl d V _ hd
    ((GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField p d V hd hs).2 hc) (hO d V hd hs hc)) (GlobalTheory.T.trace_harishChandra_induced_eq_product_characters p) (GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero p) r ρ f hρ
    (hasLabelO_of_mul O ρ hρ h0 h)⟩


end GlobalTheory.BlockTypeSplit

end
end
end
