module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimUnitaryKTypeEqDualWeylModuleStatement
public import Formalism.LocalToGlobal.HermitianForms.LastCoordinateUniformizerVectorSpansOrthogonalLi
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorWeylModuleMapsInjectiveOnPureSpanStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapFnOfEqValC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFockFormPureTensorProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TensorTypesRealPlacesEquivSpanWeylModules
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllPositiveModelFiniteDimensionalCompactType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultiplicityLiftLastChainStep
public import Formalism.LocalToGlobal.HermitianForms.TiedBrInj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsWeightEqParameterSubRho
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NegHarishChandraParamRevEqWeylWeightTop

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Rk.TopParam

def Dset (R : Ranks) (h : HCParam R) : Finset ℚ :=
  (Finset.univ.image h.v ∪ Finset.univ.image (fun j => -h.b j)) ∪
    Finset.univ.biUnion (fun j => TPar.block (-h.e j) R.t)

theorem sgHC_sub_mem (R : Ranks) (h : HCParam R) (i : ℕ) (hi : i < R.N R.m - 1) :
    sgHC R h i - (R.m * (R.t + 1) / 2 : ℚ) ∈ Dset R h := by
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  unfold sgHC Dset
  simp only [add_sub_cancel_left]
  split_ifs with h1 h2 h3
  · simp
  · apply Finset.mem_union_left; apply Finset.mem_union_right; simp
  · apply Finset.mem_union_right
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, TPar.block, Finset.mem_image, Finset.mem_range]
    refine ⟨⟨_, h2⟩, (i - (R.k - 1)) % (R.t + 1) - 1, ?_, ?_⟩
    · have := Nat.mod_lt (i - (R.k-1)) (show 0 < R.t + 1 by omega); omega
    · have : 1 ≤ (i - (R.k - 1)) % (R.t + 1) := Nat.pos_of_ne_zero h3
      push_cast [Nat.cast_sub this]; ring
  · exfalso; apply h2
    unfold Ranks.N at hi
    rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos _)]
    generalize R.m * (R.t + 1) = P at hi
    omega

theorem card_Dset_le (R : Ranks) (h : HCParam R) : (Dset R h).card ≤ R.N R.m - 1 := by
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  unfold Dset
  calc _ ≤ (Finset.univ.image h.v ∪ Finset.univ.image (fun j => -h.b j)).card
          + (Finset.univ.biUnion (fun j => TPar.block (-h.e j) R.t)).card := Finset.card_union_le _ _
    _ ≤ ((R.k - 1) + R.m) + R.m * R.t := by
        gcongr
        · refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
          · exact Finset.card_image_le.trans (by simp)
          · exact Finset.card_image_le.trans (by simp)
        · refine (Finset.card_biUnion_le_card_mul _ _ R.t ?_).trans (by simp)
          intro j _
          exact Finset.card_image_le.trans (by simp)
    _ = R.N R.m - 1 := by
        unfold Ranks.N
        have : R.m * (R.t + 1) = R.m + R.m * R.t := by ring
        rw [this]; omega

end GlobalTheory.Core.Rk.TopParam

namespace GlobalTheory.Core.Rk.TopParam

theorem neg_lam_rev_eq : ∀ (D : D7) (u : D.what₂.Word) (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)), (∀ (i : Fin (D.R.N D.R.m - 1)) τ, (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i) → ∀ τ (i : Fin D.sp.X'.rank), -M.lam τ (Fin.rev i) = (((sgT u τ).w (Fin.cast (rankP D) i) : ℤ) : ℝ) + ((rhoVec D.sp.X'.rank i : ℚ) : ℝ) := by
  intro D u M hsg τ i
  obtain ⟨hanti, q, hq, hS⟩ := M.enum τ
  have hdiv : ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℚ) = (D.R.m : ℚ) * (D.R.t + 1) / 2 := by
    obtain ⟨a, ha⟩ := D.R.m_even
    rw [Nat.cast_div (by rw [ha]; exact Dvd.intro (a * (D.R.t + 1)) (by ring)) (by norm_num)]
    push_cast; ring
  have hn : ((D.sp.X'.rank : ℕ) : ℚ) = ((D.R.N D.R.m - 1 : ℕ) : ℚ) := by rw [rankP D]
  let F : Fin D.sp.X'.rank → ℚ := fun i =>
    sgHC D.R (D.hcW u τ) (Fin.cast (rankP D) i) - (D.R.m * (D.R.t + 1) / 2 : ℚ)
  let G : Fin D.sp.X'.rank → ℚ := fun i => -q (Fin.rev i)
  have hRHS : ∀ i : Fin D.sp.X'.rank,
      (((sgT u τ).w (Fin.cast (rankP D) i) : ℤ) : ℚ) + rhoVec D.sp.X'.rank i = F i := by
    intro i
    have h1 := hsg (Fin.cast (rankP D) i) τ
    simp only [sgT, shW, F]
    rw [Int.cast_sub, h1, Int.cast_natCast, hdiv]
    simp only [rhoVec, Fin.coe_cast]
    rw [hn]; ring
  have hFa : StrictAnti F := by
    intro i j hij
    rw [← hRHS i, ← hRHS j]
    have h1 : (sgT u τ).w (Fin.cast (rankP D) j) ≤ (sgT u τ).w (Fin.cast (rankP D) i) :=
      (sgT u τ).anti (by rw [Fin.le_iff_val_le_val]; simp only [Fin.coe_cast]; exact hij.le)
    have h2 : rhoVec D.sp.X'.rank j < rhoVec D.sp.X'.rank i := by
      simp only [rhoVec]; have : (i : ℚ) < j := by exact_mod_cast hij
      linarith
    have h1' : ((sgT u τ).w (Fin.cast (rankP D) j) : ℚ) ≤ (sgT u τ).w (Fin.cast (rankP D) i) := by exact_mod_cast h1
    linarith
  have hGa : StrictAnti G := by
    intro i j hij
    have h1 := hanti (Fin.rev_lt_rev.mpr hij)
    rw [hq, hq] at h1
    have h1' : q (Fin.rev i) < q (Fin.rev j) := by exact_mod_cast h1
    simp only [G]; linarith
  have hFm : ∀ x, F x ∈ Dset D.R (D.hcW u τ) := by
    intro x
    have := sgHC_sub_mem D.R (D.hcW u τ) (Fin.cast (rankP D) x) (Fin.cast (rankP D) x).isLt
    simpa [F] using this
  have hGm : ∀ x, G x ∈ Dset D.R (D.hcW u τ) := by
    intro x
    have hmem : (q (Fin.rev x), M.ε τ (Fin.rev x)) ∈ parB (Ptw D) D.R.m τ := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hodd : ¬ Odd D.R.m := Nat.not_odd_iff_even.mpr D.R.m_even
    simp only [parB, dualPar, TPar.Dpar, Finset.mem_image, hodd, if_false, add_zero] at hmem
    obtain ⟨⟨y1, y2⟩, ⟨⟨z1, z2⟩, hz, hzy⟩, hy⟩ := hmem
    simp only [Prod.mk.injEq] at hzy hy
    obtain ⟨rfl, rfl⟩ := hzy
    have hGx : G x = z1 := by simp only [G]; rw [← hy.1]; ring
    rw [hGx]
    simp only [Dset, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_filter, Prod.mk.injEq, D.hcW_v, D.hcW_b, D.hcW_e] at hz ⊢
    rcases hz with (⟨a, ha, -⟩ | ⟨a, ha, -⟩) | ⟨a, -, w, hw, hwz, -⟩
    · exact Or.inl (Or.inl ⟨a, ha⟩)
    · exact Or.inl (Or.inr ⟨a, ha⟩)
    · exact Or.inr ⟨a, hwz ▸ hw⟩
  have hcard : (Dset D.R (D.hcW u τ)).card = D.sp.X'.rank := by
    apply le_antisymm
    · rw [rankP D]; exact card_Dset_le _ _
    · have hsub : Finset.univ.image F ⊆ Dset D.R (D.hcW u τ) := by
        intro y hy; obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy; exact hFm x
      have := Finset.card_le_card hsub
      rwa [Finset.card_image_of_injective _ hFa.injective, Finset.card_univ, Fintype.card_fin] at this
  have hFG : F ∘ Fin.rev = G ∘ Fin.rev := by
    have e1 := Finset.orderEmbOfFin_unique hcard (f := F ∘ Fin.rev) (fun x => hFm _)
      (fun a b hab => hFa (Fin.rev_lt_rev.mpr hab))
    have e2 := Finset.orderEmbOfFin_unique hcard (f := G ∘ Fin.rev) (fun x => hGm _)
      (fun a b hab => hGa (Fin.rev_lt_rev.mpr hab))
    exact e1.trans e2.symm
  have hi := congrFun hFG (Fin.rev i)
  simp only [Function.comp, Fin.rev_rev, G] at hi
  rw [hq]
  have key := congrArg (fun x : ℚ => (x : ℝ)) ((hRHS i).trans hi)
  push_cast at key
  rw [key]

end GlobalTheory.Core.Rk.TopParam
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NegHarishChandraParamRevEqWeylWeightTopStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.neg_harishChandraParam_rev_eq_weylWeight_top : ∀ (D : D7) (u : D.what₂.Word) (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)), (∀ (i : Fin (D.R.N D.R.m - 1)) τ, (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i) → ∀ τ (i : Fin D.sp.X'.rank), -M.lam τ (Fin.rev i) = (((sgT u τ).w (Fin.cast (rankP D) i) : ℤ) : ℝ) + ((rhoVec D.sp.X'.rank i : ℚ) : ℝ) := by
  first | exact @GlobalTheory.Core.Rk.TopParam.neg_lam_rev_eq | exact GlobalTheory.Core.Rk.TopParam.neg_lam_rev_eq | (intros; apply GlobalTheory.Core.Rk.TopParam.neg_lam_rev_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsJ

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms GlobalTheory.Core.Rk GlobalTheory.Core.Rk.Top
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.Top

theorem exists_isJ : ∀ (D : D7) (u : D.what₂.Word) (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)), ∃ j : SmT M →ₗ[ℂ] (FrP D → ℂ), (∀ (i : Fin (D.R.N D.R.m - 1)) τ, (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i) → IsJ u M j := by
  intro D u M
  by_cases hsg : ∀ (i : Fin (D.R.N D.R.m - 1)) τ, (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i
  swap
  · exact ⟨0, fun h => absurd h hsg⟩
  have hAP : GlobalTheory.DefLift.AllPlus M := GlobalTheory.DefLift.allPlus_of_le (Ptw D) (Nat.sub_le _ _) M
  have hε : ∀ τ, M.ε τ = allPos D.sp.X'.rank := fun τ => funext fun a => hAP τ a
  have hmod := fun τ => GlobalTheory.CompactModel.model_allPos D D.sp.X' _ M τ (hε τ)
  have hpar := GlobalTheory.T.neg_harishChandraParam_rev_eq_weylWeight_top D u M hsg
  have hpl : ∀ τ, ∃ (j : M.H τ →ₗ[ℂ] MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ) (d : ℕ)
      (b : Module.Basis (Fin d) ℂ (M.H τ)), (∀ ξ, j ξ ∈ delSq ℂ _ (sgT u τ)) ∧
      (∀ p ∈ delSq ℂ _ (sgT u τ), ∃ ξ, j ξ = p) ∧
      (∀ a a', normFock (sgT u τ) (j (b a)) (j (b a')) = if a = a' then 1 else 0) ∧
      ∀ g ∈ Matrix.unitaryGroup (Fin (D.R.N D.R.m - 1)) ℂ, ∀ ξ,
        j (M.σ τ (g.submatrix (Fin.cast (rankP D)) (Fin.cast (rankP D))) ξ) =
          (g.det ^ (-(sgT u τ).detShift)) • Formalism.GradedWeylDivisibility.rowAct ℂ gᴴ (j ξ) := fun τ => by
    have := (hmod τ).1
    exact GlobalTheory.T.finite_dim_unitary_K_type_eq_dual_weyl_module _ _ (rankP D) (sgT u τ) (M.H τ) (M.σ τ) (M.lam τ) (hmod τ).2.2.1 (hmod τ).2.2.2 (hpar τ)
  choose jH d bH hj1 hj2 hj3 hj4 using hpl
  obtain ⟨Jt, hJi, hJr, hJt⟩ := GlobalTheory.T.tensor_weyl_module_maps_injective_on_pure_span D.what₂.Tau (D.R.N D.R.m - 1) (sgT u) (fun τ => M.sm τ)
    (fun τ => jH τ ∘ₗ (M.sm τ).subtype) d (fun τ => (bH τ).map (LinearEquiv.ofTop (M.sm τ) (hmod τ).2.1).symm)
    (fun τ ξ => hj1 τ _) (fun τ p hp => by
      obtain ⟨ξ, hξ⟩ := hj2 τ p hp
      exact ⟨(LinearEquiv.ofTop (M.sm τ) (hmod τ).2.1).symm ξ, by simpa using hξ⟩)
    (fun τ a a' => by simpa using hj3 τ a a')

  set h := rankP D with hh
  let rd : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) ℂ → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ :=
    fun A => A.reindex (finCongr h) (finCongr h)
  let fr' : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ := fun τ => rd (M.fr τ)
  have hfr' : ∀ τ, IsUnit (fr' τ).det := fun τ => by
    simp only [fr', rd, Matrix.det_reindex_self]
    exact GlobalTheory.DefLift.fr_det M τ
  refine ⟨(fnOf (gramC (gramP D) (embT D)) (shiftOf (sgT u)) fr') ∘ₗ Jt, fun _ => ⟨?_, ?_, ?_⟩⟩
  · exact (Formalism.L2.Forms.fnOf_injective _ _ _ hfr').comp hJi
  · rw [LinearMap.range_comp, hJr]
    exact GlobalTheory.ValueSpaceCoordinates.map_fnOf_eq_ValC _ _ _ _ _ hfr'
  · intro τ g hg v w hw y y' hy
    classical
    obtain ⟨-, -, heval⟩ := GlobalTheory.FockTen.nfAll_ten D.what₂.Tau (D.R.N D.R.m - 1) (sgT u)
    simp only [LinearMap.comp_apply, hJt, heval]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    by_cases hρ : ρ = τ
    · subst hρ
      have hyτ : y.1 ρ = rd g * y'.1 ρ := by rw [hy ρ, Function.update_self]
      set mk := M.fr ρ * g * (M.fr ρ)⁻¹ with hmk
      have hwm : ((Function.update v ρ w ρ : M.sm ρ) : M.H ρ) = M.σ ρ mk (v ρ) := by
        rw [Function.update_self]; exact hw
      have hmk_u : mk ∈ Matrix.unitaryGroup (Fin D.sp.X'.rank) ℂ := by
        rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
        have hg' : gᴴ * ((M.fr ρ)ᴴ * M.fr ρ) * g = (M.fr ρ)ᴴ * M.fr ρ := by rw [← hAP.gram]; exact hg
        have e1 : M.fr ρ * (M.fr ρ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (GlobalTheory.DefLift.fr_det M ρ)
        calc mkᴴ * mk = ((M.fr ρ)⁻¹)ᴴ * (gᴴ * ((M.fr ρ)ᴴ * M.fr ρ) * g) * (M.fr ρ)⁻¹ := by
              simp only [hmk, Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = (M.fr ρ * (M.fr ρ)⁻¹)ᴴ * (M.fr ρ * (M.fr ρ)⁻¹) := by
              rw [hg']; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = 1 := by rw [e1, Matrix.conjTranspose_one, Matrix.one_mul]
      have hrdmul : ∀ A B, rd (A * B) = rd A * rd B := fun A B => by
        simp only [rd, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
      have hgn_u : rd mk ∈ Matrix.unitaryGroup _ ℂ := by
        rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hmk_u ⊢
        have : (rd mk)ᴴ = rd mkᴴ := by simp only [rd, Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
        rw [this, ← hrdmul, hmk_u]
        simp only [rd, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
      have hsub : (rd mk).submatrix (Fin.cast h) (Fin.cast h) = mk := by
        ext i j; simp [rd, Matrix.reindex_apply]
      have hrd : rd mk = fr' ρ * rd g * (fr' ρ)⁻¹ := by
        simp only [hmk, hrdmul, fr']
        congr 1
        simp only [rd, Matrix.inv_reindex]
      have key := hj4 ρ (rd mk) hgn_u (v ρ)
      rw [hsub] at key
      simp only [Submodule.coe_subtype]
      rw [hwm, key]
      have hoU : IsUnit ((fr' ρ)⁻¹).det := by
        rw [Matrix.det_nonsing_inv]; exact (hfr' ρ).ringInverse
      have hab : y.1 ρ = (fr' ρ)⁻¹ * rd mk * ((fr' ρ)⁻¹)⁻¹ * y'.1 ρ := by
        rw [Matrix.nonsing_inv_nonsing_inv _ (hfr' ρ), hrd, hyτ]
        simp only [Matrix.mul_assoc]
        rw [Matrix.nonsing_inv_mul_cancel_left _ _ (hfr' ρ), Matrix.nonsing_inv_mul_cancel_left _ _ (hfr' ρ)]
      have hfe := GlobalTheory.TenTypes.factor_eq (rd mk) (fr' ρ)⁻¹ (y.1 ρ) (y'.1 ρ) hgn_u hoU (shiftOf (sgT u) ρ) (jH ρ (v ρ)) hab
      rw [Matrix.nonsing_inv_nonsing_inv _ (hfr' ρ)] at hfe
      exact hfe
    · have hyρ : y.1 ρ = y'.1 ρ := by rw [hy ρ, Function.update_of_ne hρ, Matrix.one_mul]
      rw [hyρ]
      simp only [Submodule.coe_subtype, Function.update_of_ne hρ]

end GlobalTheory.Core.Rk.Top
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopReadingOfSg

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open Formalism.MainNotions.S Formalism.IndefR.Mult in
theorem GlobalTheory.SeeSaw.exists_isJ_of_par {D : D7} {u : D.what₂.Word}
    (hsg : ∀ (i : Fin (D.R.N D.R.m - 1)) τ, (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i)
    {par} (M : DSModel D.sp.X' par) (hpar : par = parB (Ptw D) D.R.m) :
    ∃ j, GlobalTheory.Core.Rk.Top.IsJ u M j := by
  subst hpar
  obtain ⟨j, hj⟩ := GlobalTheory.Core.Rk.Top.exists_isJ D u M
  exact ⟨j, hj hsg⟩

theorem GlobalTheory.SeeSaw.sg_trueColumns {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (i : Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (τ) :
    ((((I.rec7 l Z).fm u).sg τ).w i : ℚ) =
      sgHC (I.rec7 l Z).R ((I.rec7 l Z).hcW u τ) i - rhoVec ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) i := by
  have h2 := (TC.tup_sgHC_eq (B.hcW u τ) i).trans
    (congrArg (fun P => Formalism.L2.Col.RowPar.sgHC P i) (TC.tup_rowPar_eq B u τ))
  exact (Formalism.L2.Col.RowPar.sg_eq (B.hc τ) i).trans (congrArg (· - _) h2.symm)
end
end
