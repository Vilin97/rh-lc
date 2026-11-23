module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMemA
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesExistsUniqueDecompOverFrobeniusLikeEnStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsVariablePowSmulEqZeroOfFiniteLengthStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIdealDegreeBoundStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColonIdealFrobeniusLeMapExpandStatement

section

@[expose] public section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

theorem _root_.GlobalTheory.T.colonIdeal_frobenius_le_map_expand :
    ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
      [IsUnitBall O K] (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ]
      (G : Matrix κ ι K⟦X⟧),
      colon (O := O) (K := K) (G.map (frob K l)) ≤
        (colon (O := O) (K := K) G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) := by
  intro O K _ _ _ _ _ l _ ι κ _ _ G β hβ
  have map_decomp_frob {f : O⟦X⟧} {g : Fin l → O⟦X⟧}
      (h : f = ∑ j : Fin l, X ^ j.val * PowerSeries.expand l (Fact.out : l.Prime).ne_zero (g j)) :
      PowerSeries.map (algebraMap O K) f =
        ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (g j)) := by

    rw [h, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, map_X, map_expand]
    rfl
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have decO : ∀ f : O⟦X⟧, ∃! g : Fin l → O⟦X⟧,
      f = ∑ j : Fin l, X ^ j.val * PowerSeries.expand l (Fact.out : l.Prime).ne_zero (g j) :=
    GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 _
      (fun f m => coeff_expand _ _ f)
  have uniqK : ∀ f : K⟦X⟧, ∃! g : Fin l → K⟦X⟧,
      f = ∑ j : Fin l, X ^ j.val * frob K l (g j) :=
    GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 (frob K l)
      (fun f m => coeff_frob l f m)
  obtain ⟨b, hb, -⟩ := decO β
  have hbK := map_decomp_frob hb
  have key : ∀ j, b j ∈ colon (O := O) (K := K) G := by
    intro j w hw
    obtain ⟨M, hM, hMeq⟩ := hβ (frobV l w) (fun i => frob_mem_A l (hw i))
    have lift : ∀ k, ∃ μ : O⟦X⟧, PowerSeries.map (algebraMap O K) μ = M k := fun k => by
      obtain ⟨μ, hμ⟩ := (equivA O K).surjective ⟨M k, hM k⟩
      exact ⟨μ, by rw [← coe_equivA, hμ]⟩
    choose μ hμ using lift
    choose c hc using fun k => (decO (μ k)).exists
    have hMk : ∀ k, M k = ∑ j : Fin l, X ^ j.val *
          frob K l (PowerSeries.map (algebraMap O K) (c k j)) :=
      fun k => by rw [← hμ k]; exact map_decomp_frob (hc k)
    refine ⟨fun k => PowerSeries.map (algebraMap O K) (c k j), fun k => map_mem_A _, ?_⟩
    funext i
    have e1 := congrFun hMeq i
    simp only [Pi.smul_apply, smul_eq_mul, frobV_apply] at e1
    obtain ⟨g, -, hg⟩ := uniqK (PowerSeries.map (algebraMap O K) β * frob K l (w i))
    have E1 : PowerSeries.map (algebraMap O K) β * frob K l (w i) =
        ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (b j) * w i) := by
      rw [hbK, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_assoc]
    have E2 : PowerSeries.map (algebraMap O K) β * frob K l (w i) =
        ∑ j : Fin l, X ^ j.val *
          frob K l ((G *ᵥ fun k => PowerSeries.map (algebraMap O K) (c k j)) i) := by
      rw [e1]

      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hMk, Finset.mul_sum, map_sum, map_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have h1 := hg _ E1
    have h2 := hg _ E2
    rw [Pi.smul_apply, smul_eq_mul]
    exact (congrFun h1 j).trans (congrFun h2 j).symm
  rw [hb]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (key j))
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColonIdealMapExpandLeFrobeniusStatement

section

@[expose] public section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

theorem _root_.GlobalTheory.T.colonIdeal_map_expand_le_frobenius : ∀ (O K : Type)
    [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ] (G : Matrix κ ι K⟦X⟧),
    (colon (O := O) (K := K) G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) ≤
      colon (O := O) (K := K) (G.map (frob K l)) := by
  intro O K _ _ _ _ _ l _ ι κ _ _ G
  rw [Ideal.map_le_iff_le_comap]
  intro α hα
  rw [Ideal.mem_comap]
  intro w hw
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hf : ∀ i, ∃ f : O⟦X⟧, PowerSeries.map (algebraMap O K) f = w i := fun i => by
    obtain ⟨f, hf⟩ := (equivA O K).surjective ⟨w i, hw i⟩
    exact ⟨f, by rw [← coe_equivA, hf]⟩
  choose f hf using hf
  have hdec := fun i => (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 (PowerSeries.expand l (Fact.out : l.Prime).ne_zero)
    (fun g m => PowerSeries.coeff_expand _ _ g) (f i)).exists
  choose g hg using hdec
  have hα' := fun j : Fin l => hα (fun i => PowerSeries.map (algebraMap O K) (g i j))
    (fun i => map_mem_A _)
  choose m hm hmeq using hα'
  have hX : (X : K⟦X⟧) ∈ A O K := by simpa using map_mem_A (O := O) (K := K) X
  refine ⟨∑ j : Fin l, (X : K⟦X⟧) ^ j.val • frobV l (m j), fun i => ?_, ?_⟩
  · rw [Finset.sum_apply]
    refine Subalgebra.sum_mem _ fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, frobV_apply]
    exact mul_mem (pow_mem hX _) (frob_mem_A l (hm j i))
  · funext i
    have hwi : w i = ∑ j : Fin l, (X : K⟦X⟧) ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (g i j)) := by

      rw [← hf i, hg i, map_sum]
      simp [map_mul, map_pow, map_X, map_expand, frob]
    have key : ∀ j : Fin l, frob K l (PowerSeries.map (algebraMap O K) α) *
        frob K l (PowerSeries.map (algebraMap O K) (g i j)) = (G.map (frob K l) *ᵥ frobV l (m j)) i := by
      intro j
      rw [← map_mul]
      have := congrFun (hmeq j) i
      rw [Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      exact RingHom.map_mulVec (frob K l).toRingHom G (m j) i
    rw [Pi.smul_apply, smul_eq_mul, map_expand, hwi, Finset.mul_sum, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← key j]
    simp only [frob]
    ring
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowMulMemColonIdealFrobenius

section

@[expose] public section

noncomputable section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

namespace GlobalTheory.LiftCoker

theorem E_pow_mul_mem_colon_frob (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ)
    (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (τ : ZMod a) :
    ∀ α ∈ colon O K (F.mat τ),
      (X ^ e + (l : O⟦X⟧)) ^ (H + η) * α ∈ colon O K ((F.mat (τ - 1)).map (frob K l)) := by
  intro α hα w hw
  set x := D₂.mx τ *ᵥ w with hxdef
  have hx : x ∈ D₂.Lcomp τ := D₂.mem_extc.2 ⟨w, hw, rfl⟩
  have hxL : (Pi.single τ x : Vec K a κ) ∈ D₂.L := mem_tot.2 fun σ => by
    by_cases h : σ = τ
    · subst h
      simpa using hx
    · simp [h, zero_mem]
  have hup := mem_tot.1 (D₂.upper _ hxL) τ
  simp only [Pi.smul_apply, Pi.single_eq_same] at hup
  obtain ⟨m, hm, hαm⟩ := hα (E K l e ^ η • x) hup
  have hmM : (Pi.single τ m : Vec K a ι) ∈ D₁.M := mem_tot.2 fun σ => by
    by_cases h : σ = τ
    · subst h
      rw [Pi.single_eq_same]
      exact hm
    · simp [h, zero_mem]
  have hlow := mem_tot.1 (D₁.lower _ hmM) τ
  simp only [Pi.smul_apply, Pi.single_eq_same] at hlow
  obtain ⟨m', hm', hm'eq⟩ := D₁.mem_extc.1 hlow
  have hE : PowerSeries.map (algebraMap O K) ((X ^ e + (l : O⟦X⟧)) ^ (H + η) * α) =
      E K l e ^ (H + η) * PowerSeries.map (algebraMap O K) α := by
    simp [E, map_X, map_natCast]
  refine ⟨m', hm', ?_⟩
  · have key : D₂.mx τ *ᵥ (PowerSeries.map (algebraMap O K) ((X ^ e + (l : O⟦X⟧)) ^ (H + η) * α) • w) =
        D₂.mx τ *ᵥ ((F.mat (τ - 1)).map (frob K l) *ᵥ m') := by
      rw [Matrix.mulVec_smul, ← hxdef, hE, pow_add,
        show E K l e ^ H * E K l e ^ η * PowerSeries.map (algebraMap O K) α =
          E K l e ^ H * (PowerSeries.map (algebraMap O K) α * E K l e ^ η) by ring,
        mul_smul, mul_smul, hαm,
        ← Matrix.mulVec_smul, hm'eq, Matrix.mulVec_mulVec, F.comm, ← Matrix.mulVec_mulVec]
    have := congrArg (fun v => D₂.mxInv τ *ᵥ v) key
    rwa [Matrix.mulVec_mulVec (M := D₂.mxInv τ) (N := D₂.mx τ),
      Matrix.mulVec_mulVec (M := D₂.mxInv τ) (N := D₂.mx τ), PhiMod.mxInv_mul_mx,
      Matrix.one_mulVec, Matrix.one_mulVec] at this

end GlobalTheory.LiftCoker
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowMulMemColonIdealFrobeniusStatement

section

@[expose] public section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

theorem _root_.GlobalTheory.T.eisenstein_pow_mul_mem_colonIdeal_frobenius : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (τ : ZMod a), ∀ α ∈ colon O K (F.mat τ), (X ^ e + (l : O⟦X⟧)) ^ (H + η) * α ∈ colon O K ((F.mat (τ - 1)).map (frob K l)) := by
  first | exact @GlobalTheory.LiftCoker.E_pow_mul_mem_colon_frob | exact GlobalTheory.LiftCoker.E_pow_mul_mem_colon_frob | (intros; apply GlobalTheory.LiftCoker.E_pow_mul_mem_colon_frob <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VPowLatticeLeImageAddLPowOfFiniteCokernel

section

@[expose] public section

noncomputable section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

theorem GlobalTheory.LiftCoker.vPow_mem_imL_add_lPow : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), IsFiniteLength (A O K) F.coker → ∀ b : ℕ, 1 ≤ b → H + η + b ≤ l → ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L, ((X : K⟦X⟧) ^ e) ^ (H + η + b) • x = F.app y + (l : K) ^ b • z := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₁ D₂ F hfin b hb hlb x hx
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_variable_pow_smul_eq_zero_of_finiteLength O K _ hfin
  have hX : ∀ τ, (X : O⟦X⟧) ^ n ∈ colon O K (F.mat τ) := by
    intro τ w hw
    have hW : (Pi.single τ w : Vec K a κ) ∈ D₂.M := mem_tot.2 fun σ i => by
      by_cases h : σ = τ
      · subst h; simpa using hw i
      · simp [h]
    have h1 := hn (Submodule.Quotient.mk ⟨_, hW⟩)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap] at h1
    obtain ⟨m, hm, hm'⟩ := h1
    refine ⟨m τ, fun j => mem_tot.1 hm τ j, ?_⟩
    have h2 := congrFun hm' τ
    simp only [LinearMap.restrictScalars_apply, BK.Hom.app_apply] at h2
    rw [h2]
    simp [Submodule.coe_smul, Subalgebra.smul_def]
  have key := GlobalTheory.T.X_pow_mem_map_sup_span_pow_of_frobenius_bound (O := O) l hl2 (PowerSeries.expand l (Fact.out : l.Prime).ne_zero)
    (fun f m => PowerSeries.coeff_expand _ _ f) a e (H + η) b (fun τ => colon O K (F.mat τ)) hb hlb
    (fun τ => ⟨n, Ideal.mem_sup_left (hX τ)⟩)
    (fun τ α hα => GlobalTheory.T.colonIdeal_frobenius_le_map_expand O K l ι κ _ (GlobalTheory.T.eisenstein_pow_mul_mem_colonIdeal_frobenius O K l e a ι κ η H D₁ D₂ F τ α hα))
  have comp : ∀ τ, ∀ w : κ → K⟦X⟧, (∀ i, w i ∈ A O K) → ∃ m : ι → K⟦X⟧, (∀ j, m j ∈ A O K) ∧
      ∃ w' : κ → K⟦X⟧, (∀ i, w' i ∈ A O K) ∧
        ((X : K⟦X⟧) ^ e) ^ (H + η + b) • w = (F.mat (τ - 1)).map (frob K l) *ᵥ m + (l : K⟦X⟧) ^ b • w' := by
    intro τ w hw
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (key (τ - 1))
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hq
    obtain ⟨m, hm, hmeq⟩ := GlobalTheory.T.colonIdeal_map_expand_le_frobenius O K l ι κ _ hp w hw
    refine ⟨m, hm, PowerSeries.map (algebraMap O K) c • w, fun i => ?_, ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul]
      exact mul_mem (map_mem_A c) (hw i)
    · have h3 := congrArg (PowerSeries.map (algebraMap O K)) hpq
      rw [map_add (f := _), map_mul, map_pow, map_pow, map_X, map_natCast] at h3
      rw [← pow_mul, ← h3, add_smul, hmeq, smul_smul, mul_comm]
  choose w hw hxw using fun τ => D₂.mem_extc.1 (mem_tot.1 hx τ)
  choose m hm w' hw' hmw using fun τ => comp τ (w τ) (hw τ)
  refine ⟨fun τ => D₁.mx τ *ᵥ m τ, mem_tot.2 fun τ => D₁.mem_extc.2 ⟨m τ, hm τ, rfl⟩,
    fun τ => D₂.mx τ *ᵥ w' τ, mem_tot.2 fun τ => D₂.mem_extc.2 ⟨w' τ, hw' τ, rfl⟩, ?_⟩
  funext τ
  have hsm : ∀ v : κ → K⟦X⟧, (l : K) ^ b • v = (l : K⟦X⟧) ^ b • v := fun v => by
    rw [← algebraMap_smul K⟦X⟧ ((l : K) ^ b) v, map_pow, map_natCast]
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hsm, BK.Hom.app_apply, Matrix.mulVec_mulVec,
    F.comm τ, hxw τ, ← Matrix.mulVec_smul, hmw τ, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VPowLatticeLeImageAddLPowOfFiniteCokernelStatement

section

@[expose] public section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.vPow_lattice_le_image_add_lPow_of_finite_cokernel : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), IsFiniteLength (A O K) F.coker → ∀ b : ℕ, 1 ≤ b → H + η + b ≤ l → ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L, ((X : K⟦X⟧) ^ e) ^ (H + η + b) • x = F.app y + (l : K) ^ b • z := by
  first | exact @GlobalTheory.LiftCoker.vPow_mem_imL_add_lPow | exact GlobalTheory.LiftCoker.vPow_mem_imL_add_lPow | (intros; apply GlobalTheory.LiftCoker.vPow_mem_imL_add_lPow <;> assumption)
end
end
