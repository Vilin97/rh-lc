module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedParahoricBlockVectorOfIdempotentStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParabolicTypeVectorOfEquivariantMapStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsConstituentOfRepIsoLeft
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.Basic.PEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetSubquotientDetCharacterFactorsIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetSubquotientFirstFactorOfEmptySecondBlockStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionEmptySecondIsSubquotientFirstStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitLocalOfGreen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameCharacterParahoricInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharInCuspidalSupportOfJacquetSubquotientFactorStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLeviBlockEigenvectorAtIdentityStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InSupportMulUnramifiedCharOfIntegralEigenvectorStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSplitExactTwistCountProductStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRepParabolicCharStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParahoricBlockTypeVectorCuspidalSupportTameCharaStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalTwistOfBlockTypeVectorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInduction
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalSeriesConcreteOfDzSwap
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapOfLevelTypeVector

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

theorem exists_map_of_typeVec (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] (n : Type) [Fintype n] [DecidableEq n] (W : Type) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL n F) W) (ρ : FDRep ℂ (GL n (ZMod p))) (y : W) :
    resCard F = p → TypeVec π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) y → ∃ φ : ρ →ₗ[ℂ] W, φ ≠ 0 ∧
      ∀ (g : GL n (ZMod p)) (h : GL n F), IsLift g h → ∀ w, π h (φ w) = φ (ρ.ρ g w) := by
  intro hp hy
  obtain ⟨h1, ℓ, hℓ, h0⟩ := hy
  let Φ : Module.Dual ℂ ρ → (ρ →ₗ[ℂ] W) := fun μ =>
    ∑ g : GL n (ZMod p), LinearMap.smulRight (μ ∘ₗ ρ.ρ g⁻¹) (π (ℓ g) y)
  have hΦ : ∀ μ w, Φ μ w = ∑ g, μ (ρ.ρ g⁻¹ w) • π (ℓ g) y := by
    intro μ w
    simp [Φ, LinearMap.sum_apply]
  have heq : ∀ μ (g₀ : GL n (ZMod p)) (h : GL n F), IsLift g₀ h → ∀ w, π h (Φ μ w) = Φ μ (ρ.ρ g₀ w) := by
    intro μ g₀ h H w

    rw [hΦ, hΦ, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g₀) _ _ fun g => ?_
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, IsLift.apply_eq hp h1 (H.mul hp (hℓ g)) (hℓ _)]
    simp [mul_inv_rev, map_mul, Module.End.mul_apply]
  by_contra hne
  have hz : ∀ μ, Φ μ = 0 := fun μ => by
    by_contra e
    exact hne ⟨_, e, heq μ⟩
  apply h0
  let b := Module.finBasis ℂ ρ
  have key : ∑ g, LinearMap.trace ℂ ρ (ρ.ρ g⁻¹) • π (ℓ g) y = 0 := by
    have : ∑ i, Φ (b.coord i) (b i) = 0 := by simp [hz]
    rw [← this]
    simp_rw [hΦ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_smul, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rfl
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp_rw [Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff, mul_smul]
  rw [← Finset.smul_sum, key, smul_zero]

end GlobalTheory.LevelType
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapOfLevelTypeVectorStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_equivariantMap_of_levelTypeVector : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (n : Type) [Fintype n] [DecidableEq n] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL n F) W) (ρ : FDRep ℂ (GL n (ZMod p))) (y : W), resCard F = p → TypeVec π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) y → ∃ φ : ρ →ₗ[ℂ] W, φ ≠ 0 ∧ ∀ (g : GL n (ZMod p)) (h : GL n F), IsLift g h → ∀ w, π h (φ w) = φ (ρ.ρ g w) := by
  first | exact @GlobalTheory.LevelType.exists_map_of_typeVec | exact GlobalTheory.LevelType.exists_map_of_typeVec | (intros; apply GlobalTheory.LevelType.exists_map_of_typeVec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientRepresentationTwoReindexings

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

theorem reix_eq_conj (R : Type) [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (φ φ' : m ≃ n) : ∃ w : GL n R, ∀ g : GL m R, reix R φ g * w = w * reix R φ' g := by
  let e : n ≃ n := φ'.symm.trans φ
  have h1 : ((e.symm.toPEquiv.toMatrix : Matrix n n R) * e.toPEquiv.toMatrix) = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  have h2 : ((e.toPEquiv.toMatrix : Matrix n n R) * e.symm.toPEquiv.toMatrix) = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  let w : GL n R := ⟨e.symm.toPEquiv.toMatrix, e.toPEquiv.toMatrix, h1, h2⟩
  refine ⟨w, fun g => ?_⟩
  have key : (reix R φ g).val = w.val * (reix R φ' g).val * w⁻¹.val := by
    change _ = e.symm.toPEquiv.toMatrix * _ * e.toPEquiv.toMatrix
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    simp [val_reix, e]
  apply Units.ext
  rw [Units.val_mul, key, mul_assoc, Units.inv_mul, mul_one, Units.val_mul]

theorem subquotient_reix (R : Type) [CommRing R] (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (φ φ' : m ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL n R) V) :
    IsSubquotient (σ.comp (reix R φ) : Representation ℂ (GL m R) V) (σ.comp (reix R φ') : Representation ℂ (GL m R) V) := by
  obtain ⟨w, hw⟩ := reix_eq_conj R φ φ'
  refine IsSubquotient.of_surjective ⟨σ w, fun g => ?_⟩ fun v => ⟨σ w⁻¹ v, ?_⟩
  · change σ w * σ (reix R φ' g) = σ (reix R φ g) * σ w
    rw [← map_mul, ← map_mul, hw]
  · change σ w (σ w⁻¹ v) = v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

end GlobalTheory.LevelType
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientRepresentationTwoReindexingsStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isSubquotientRepresentation_two_reindexings : ∀ (R : Type) [CommRing R] (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (φ φ' : m ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL n R) V), IsSubquotient (σ.comp (reix R φ) : Representation ℂ (GL m R) V) (σ.comp (reix R φ') : Representation ℂ (GL m R) V) := by
  first | exact @GlobalTheory.LevelType.subquotient_reix | exact GlobalTheory.LevelType.subquotient_reix | (intros; apply GlobalTheory.LevelType.subquotient_reix <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisBlockTypeSplit

section

@[expose] public section



section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.BlockTypeSplit
open ValuativeRel Polynomial
section Finite
end Finite
section Local
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {p : ℕ} [Fact p.Prime] {r t : ℕ}
theorem block_type_split_local_alt (hP : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hp : resCard F = p) (L : GlobalTheory.GLq.LabelDatum p) {χ : Fˣ →* ℂˣ}
    (hχ : IsSmoothChar χ) (hχt : IsTame χ) {θ : (ZMod p)ˣ →* ℂˣ} (hθχ : CharLift θ χ) {u : ZMod p}
    (hθ : GlobalTheory.GLp.IsCharLab L θ u) (π : Irr F (r + t)) (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (hρ : CategoryTheory.Simple ρ)
    {f : (ZMod p)[X]} (hf : GlobalTheory.GLq.HasLabel L (fun x => ρ.character x) f) (hu : ¬ f.IsRoot u) {x : π.V}
    (hx : IsBlockVec χ π.π x) (hxρ : NotKilled π.π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) x) :
    ∃ (π₁ : Irr F r) (π₂ : Irr F t), IsSpherical π₂.π ∧
      Nonempty (π.π.Equiv (prod₂ π₁.π (_root_.GlobalTheory.SmGL.twist π₂.π (detChar (Fin t) χ)))) ∧
      ∃ y, IsLevelOne π₁.π y ∧ NotKilled π₁.π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) y := by
  classical
  have hBZ := hP.bz
  have hG := hP.geo
  have hM := hP.mp
  obtain ⟨v, hv, hb, ℓ, hℓ, hzv⟩ := GlobalTheory.T.exists_fixed_parahoricBlockVector_of_idempotent F p r t χ _ π.π _ x hp (GlobalTheory.SerOSys.zIdem_idem_central ρ hρ).1 hx hxρ
  obtain ⟨Y, _, _, τ, hτ, hsub, y, hy0, hy, hyρ⟩ :=
    GlobalTheory.T.tame_character_parahoric_invariant hM F p r t χ _ π.π _ v ℓ hp π.smooth π.irr hχt hv hb hℓ hzv
  obtain ⟨s, d, σ, hsupp, hle⟩ := GlobalTheory.T.parahoricBlockTypeVector_cuspidalSupport_tame_characters hBZ hG hP.unl hM F r t χ π v hχ hχt hv hb
  rcases hle.lt_or_eq with hlt | heq
  · exfalso
    obtain ⟨-, hσ, e₀, hπσ⟩ := hsupp
    obtain ⟨b, fr, gc, S, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG F).1 (hG F).2 e₀
      (two (stdSum (rfl : r + t = r + t))) (fun a => (σ a).smooth)
      (fun a => hasFiniteLength_of_isIrreducible (σ a).irr) hτ
      (hsub.trans (isSubquotient_jac_two _ (isSmooth_parInd _ _) hπσ))
    set A := {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar F α)))} with hA
    obtain ⟨i, hi, hi0⟩ : ∃ i ∈ A, b.1 i true = 0 := by
      by_contra! hc
      have h2 := b.2.2 true
      have h3 : A.ncard ≤ ∑ i, b.1 i true := by
        rw [Set.ncard_eq_toFinset_card' A, Finset.card_eq_sum_ones]
        exact (Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.2 (hc i (Set.mem_toFinset.1 hi))).trans
          (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
      simp only [Fintype.card_fin] at h2
      omega
    obtain ⟨hd, α, hα⟩ := hi
    have hi1 : b.1 i false = 1 := by
      have h1 := b.2.1 i
      simp [Fintype.sum_bool] at h1
      omega
    have hact := GlobalTheory.T.jacquetSubquotient_detCharacter_factors_integral F _ Bool (b.1 i) (fr i) _ (σ i).π _ (S i) hα (hrow i) false
    obtain ⟨w, hw⟩ := typeVec_first (fun j => multiProd (gc j) fun i => (S i j).ρ) (fun j => isSmooth_parInd _ _) hcol hyρ
    obtain ⟨φ, hφ0, hφ⟩ := GlobalTheory.T.exists_equivariantMap_of_levelTypeVector F p (Fin r) _ _ ρ w hp hw
    obtain ⟨v', hv', hpar⟩ := GlobalTheory.T.exists_parabolicTypeVector_of_equivariantMap F p (Fin s) (Fin r) (fun i => Fin (b.1 i false)) (gc false) _
      (fun i => (S i false).ρ) i θ χ _ ρ.ρ φ hp hθχ (fun g hg v => by
        rw [hact g hg v, MonoidHom.mul_apply,
          isUnram_unrChar F α _ (GlobalTheory.StepData.valuation_det_of_mem_KO hg), mul_one]) hφ0 hφ
    exact hu (isRoot_of_parVec L (gc false) i ρ hρ hf hθ (by rw [Fintype.card_fin, hi1]) hv' hpar)
  · obtain ⟨π₁, π₂, ⟨φ⟩, hno⟩ := GlobalTheory.T.irreducible_split_exact_twistCount_product hBZ hG hP.unl F r t χ π s d σ hχ hsupp heq.symm
    have hsph := GlobalTheory.T.spherical_twist_of_blockTypeVector hBZ hG hM F r t χ π π₁ π₂ v hχ hχt hno ⟨φ⟩ hv hb
    refine ⟨π₁, GlobalTheory.SplitPairLift.twistIrr π₂ hχ.inv, hsph, ?_, ?_⟩
    · have h := GlobalTheory.SplitPairLift.twist_twist_inv π₂ χ⁻¹
      rw [inv_inv] at h
      show Nonempty (π.π.Equiv (prod₂ π₁.π (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.SmGL.twist π₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ))))
      rw [h]
      exact ⟨φ⟩
    obtain ⟨E⟩ := Exponents.prod₂_equiv_multiProd F r t _ _ π₁.π π₂.π
    let Ψ := φ.trans E
    have hρs : ∀ i, IsSmooth (Exponents.twoRep π₁.π π₂.π i) := fun i => by
      cases i
      · exact π₁.smooth
      · exact π₂.smooth
    have hρl : ∀ i, HasFiniteLength (Exponents.twoRep π₁.π π₂.π i) := fun i => by
      cases i
      · exact hasFiniteLength_of_isIrreducible π₁.irr
      · exact hasFiniteLength_of_isIrreducible π₂.irr
    obtain ⟨b, fr, gc, S, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG F).1 (hG F).2
      (two (stdSum (rfl : r + t = r + t))) (two (stdSum (rfl : r + t = r + t))) hρs hρl hτ
      (hsub.trans (isSubquotient_jac_two _ (isSmooth_parInd _ _)
        (IsSubquotient.of_injective Ψ.toIntertwiningMap Ψ.toLinearEquiv.injective)))
    obtain ⟨z, hz0, hz⟩ := GlobalTheory.T.levi_rep_parabolic_char F Bool (Two (Fin r) (Fin t)) _ (fun j => multiProd (gc j) fun i => (S i j).ρ)
      Y τ true χ y (fun j => isSmooth_parInd _ _) hχ hcol hy0 hy
    obtain ⟨w, hw0, hw⟩ := GlobalTheory.T.exists_levi_block_eigenvector_at_identity F Bool (fun i => Fin (b.1 i true)) (Fin t) (gc true) _
      (fun i => (S i true).ρ) χ z hz0 hz
    have hm : b.1 false true = 0 := by
      by_contra hm
      obtain ⟨z', hz'0, hz'⟩ := GlobalTheory.T.levi_rep_parabolic_char F Bool (fun i => Fin (b.1 i true)) _ (fun i => (S i true).ρ) _
        (piTensor fun i => (S i true).ρ) false χ w (fun i => (S i true).smooth) hχ (IsSubquotient.refl _) hw0 (hw false)
      obtain ⟨α, hα⟩ := GlobalTheory.T.inSupport_mul_unramifiedChar_of_integralEigenvector hBZ hG hM F _ _ (S false true).ρ χ z' (S false true).smooth (S false true).irr hχ
        (Nat.pos_of_ne_zero hm) hz'0 hz'
      exact hno α (GlobalTheory.T.charInCuspidalSupport_of_jacquet_subquotient_factor hBZ hG F r _ π₁.π Bool (b.1 false) (fr false) (S false) true _ π₁.smooth (hrow false) hα)
    have hm' : b.1 true false = 0 := by
      have h1 := b.2.1 false
      have h2 := b.2.2 false
      simp [Fintype.sum_bool] at h1 h2
      omega
    obtain ⟨w₁, hw₁⟩ := typeVec_first (fun j => multiProd (gc j) fun i => (S i j).ρ) (fun j => isSmooth_parInd _ _) hcol hyρ
    obtain ⟨φ₁, h1⟩ := GlobalTheory.T.jacquetSubquotient_firstFactor_of_emptySecondBlock F r (b.1 false) (fr false) _ π₁.π (S false) hm (hrow false)
    obtain ⟨φ₂, h2⟩ := GlobalTheory.T.parabolicInduction_emptySecond_isSubquotient_first F r (fun i => b.1 i false) (gc false) (fun i => S i false) hm'
    obtain ⟨y₁, hy₁⟩ := TypeVec.up π₁.smooth (h2.trans ((GlobalTheory.T.isSubquotientRepresentation_two_reindexings F _ _ φ₂ φ₁ _ (S false false).ρ).trans h1)) hw₁
    exact ⟨y₁, typeVec_iff _ _ _ hy₁⟩
end Local
open Formalism.BasicNotions GlobalTheory.HeightCounting in
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D),
    GreenLab Γ → _root_.GlobalTheory.PendOf.SplitLocalCondition hL D := by
  intro hP hL D Γ hΓ k v χ hχ u π ρ f ht hlab hser hu ⟨x, hx, hxρ⟩
  have hchi := _root_.UpperTheory.Lit.Dz.localGlobalCompatibility_cmDatum_alt hL D Γ k v χ hχ u ht hlab
  have h0 : idemOf D k ρ ≠ 0 := fun e => by
    obtain ⟨ℓ, -, h⟩ := hxρ
    refine h ?_
    rw [e]
    simp
  obtain ⟨L, h1, h2, hf⟩ := @exists_hasLabel _ ⟨D.host.g_prime k⟩ _ (D.ntypes.teichC_inj k) _ (Γ.ζ_gen k) (Γ.O k) (hΓ k)
    _ ρ hser.1 f h0 (by rw [← Γ.eSer_def]; exact hser.2)
  refine (And.right hchi L h1 h2).elim fun θ hθ => ?_
  exact @_root_.GlobalTheory.BlockTypeSplit.block_type_split_local_alt _ _ _ _ _ _ ⟨D.host.g_prime k⟩ _ _ hP (And.left hchi) L χ hχ ht θ hθ.1 u hθ.2 π ρ hser.1 f hf hu x hx hxρ
end GlobalTheory.BlockTypeSplit
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.splitLoc_of_greenLab_depth_zero : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D), GreenLab Γ → _root_.GlobalTheory.PendOf.SplitLocalCondition hL D := by
  first | exact @_root_.GlobalTheory.BlockTypeSplit.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.BlockTypeSplit.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.BlockTypeSplit.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end
end
