module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittSt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSLocSB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlgWitt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LamAE
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittAlg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittOEv
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSKfOrb
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittGS

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittAlg

open Matrix Formalism.UG

section GS

variable {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (J : Matrix (Fin n) (Fin n) K)

theorem exists_aniso (hσ : ∀ z, σ (σ z) = z) (hJ : IsHerm σ J) (h2 : (2 : K) ≠ 0) (u w : Fin n → K)
    (huw : hform σ J u w ≠ 0) : ∃ r t : K, hform σ J (r • u + t • w) (r • u + t • w) ≠ 0 := by
  by_contra H
  push Not at H
  have hexp : ∀ r t : K, hform σ J (r • u + t • w) (r • u + t • w) =
      σ r * r * hform σ J u u + σ r * t * hform σ J u w + σ t * r * hform σ J w u +
        σ t * t * hform σ J w w := by
    intro r t
    simp only [hform_add_left, hform_add_right, hform_smul_left, hform_smul_right]
    ring
  set q := hform σ J u w with hq
  set t : K := 2⁻¹ / q with htdef
  have h1 := H 1 0
  have h2' := H 0 1
  have h3 := H 1 t
  rw [hexp, map_one, map_zero] at h1 h2'
  rw [hexp, map_one] at h3
  have ht : t * q = 2⁻¹ := div_mul_cancel₀ _ huw
  have hst : σ t * hform σ J w u = 2⁻¹ := by
    rw [← hform_conj σ J hσ hJ u w, ← hq, ← map_mul, ht, map_inv₀, map_ofNat]
  have hinv : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  exact one_ne_zero (by linear_combination h3 - h1 - (σ t * t) * h2' - ht - hst - hinv : (1 : K) = 0)

end GS

theorem hermDiag : Formalism.L2.SG.Pf.NcS.IntWittPf.HermDiag := by
  intro K _ σ hσ h2 n J hJ a X0 hT
  classical
  have hconj := hform_conj σ J hσ hJ
  let W : Submodule K (Fin n → K) := Submodule.span K (Set.range X0)
  let comb : (Fin a → K) → (Fin n → K) := fun c => ∑ l, c l • X0 l
  have hN : ∀ c : Fin a → K, (∀ j, hform σ J (X0 j) (comb c) = 0) → c = 0 := by
    intro c hc
    refine Matrix.eq_zero_of_mulVec_eq_zero hT ?_
    funext j
    have e : hform σ J (X0 j) (∑ l, c l • X0 l) = 0 := hc j
    rw [hform_sum_right] at e
    simp only [mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← e]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hcW : ∀ c, comb c ∈ W := fun c => W.sum_mem fun l _ => W.smul_mem _ (Submodule.subset_span ⟨l, rfl⟩)
  have main : ∀ k ≤ a, ∃ Z : Fin k → Fin n → K, (∀ i, Z i ∈ W) ∧
      (∀ i j, i ≠ j → hform σ J (Z i) (Z j) = 0) ∧ ∀ i, hform σ J (Z i) (Z i) ≠ 0 := by
    intro k
    induction k with
    | zero => intro _; exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨Z, hZW, hZo, hZd⟩ := ih (by omega)
      let f : (Fin a → K) →ₗ[K] (Fin k → K) :=
        { toFun := fun c i => hform σ J (Z i) (comb c)
          map_add' := by
            intro c d
            funext i
            simp only [comb, Pi.add_apply, add_smul, Finset.sum_add_distrib, hform_add_right]
          map_smul' := by
            intro r c
            funext i
            simp only [comb, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← smul_smul, ← Finset.smul_sum,
              hform_smul_right] }
      have hlt : Module.finrank K (Fin k → K) < Module.finrank K (Fin a → K) := by
        simp only [Module.finrank_fin_fun]
        omega
      obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)
      have hcZ : ∀ i, hform σ J (Z i) (comb c) = 0 := fun i => congrFun (LinearMap.mem_ker.1 hc) i
      obtain ⟨j, hj⟩ : ∃ j, hform σ J (X0 j) (comb c) ≠ 0 := by
        by_contra H
        push Not at H
        exact hc0 (hN c H)
      let w := X0 j - ∑ i, (hform σ J (Z i) (X0 j) / hform σ J (Z i) (Z i)) • Z i
      have hwZ : ∀ m, hform σ J (Z m) w = 0 := by
        intro m
        simp only [w, hform_sub_right, hform_sum_right]
        rw [Finset.sum_eq_single m]
        · rw [div_mul_cancel₀ _ (hZd m), sub_self]
        · intro i _ him
          rw [hZo m i (Ne.symm him), mul_zero]
        · simp
      have hwc : hform σ J w (comb c) ≠ 0 := by
        simp only [w, hform_sub_left, hform_sum_left]
        rw [Finset.sum_eq_zero, sub_zero]
        · exact hj
        · intro i _
          rw [hcZ i, mul_zero]
      have hwW : w ∈ W := W.sub_mem (Submodule.subset_span ⟨j, rfl⟩) (W.sum_mem fun i _ => W.smul_mem _ (hZW i))
      obtain ⟨r, t, hz⟩ := exists_aniso σ J hσ hJ h2 w (comb c) hwc
      set z := r • w + t • comb c with hzdef
      have hzZ : ∀ m, hform σ J (Z m) z = 0 := by
        intro m
        rw [hzdef, hform_add_right, hform_smul_right, hform_smul_right, hwZ, hcZ, mul_zero, mul_zero, add_zero]
      refine ⟨Fin.snoc Z z, ?_, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · rw [Fin.snoc_last]
          exact W.add_mem (W.smul_mem _ hwW) (W.smul_mem _ (hcW c))
        · rw [Fin.snoc_castSucc]
          exact hZW i
      · intro i j
        refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
        · intro h; exact absurd rfl h
        · intro _
          rw [Fin.snoc_last, Fin.snoc_castSucc, ← hconj, hzZ, map_zero]
        · intro _
          rw [Fin.snoc_last, Fin.snoc_castSucc]
          exact hzZ i
        · intro hij
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hZo i j (fun e => hij (by rw [e]))
      · intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · rw [Fin.snoc_last]
          exact hz
        · rw [Fin.snoc_castSucc]
          exact hZd i
  obtain ⟨Z, hZW, hZo, hZd⟩ := main a le_rfl
  have hex : ∀ i, ∃ c : Fin a → K, ∑ l, c l • X0 l = Z i :=
    fun i => (Submodule.mem_span_range_iff_exists_fun K).1 (hZW i)
  choose C hC using hex
  let P : Matrix (Fin a) (Fin a) K := Matrix.of C
  have hPX : ∀ i, ∑ l, P i l • X0 l = Z i := fun i => hC i
  have hdet : P.det ≠ 0 := by
    intro hd
    obtain ⟨c, hc0, hcP⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    apply hc0
    funext j
    have e : ∑ i, c i • Z i = 0 := by
      have hl : ∀ l, ∑ i, c i * P i l = 0 := fun l => by
        have := congrFun hcP l
        simpa [vecMul, dotProduct] using this
      simp_rw [← hPX, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, hl, zero_smul, Finset.sum_const_zero]
    have h := congrArg (hform σ J (Z j)) e
    rw [hform_sum_right, hform_zero_right, Finset.sum_eq_single j] at h
    · exact (mul_eq_zero.1 h).resolve_right (hZd j)
    · intro i _ hij
      rw [hZo j i (Ne.symm hij), mul_zero]
    · simp
  refine ⟨P, P⁻¹, Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.2 hdet), ?_, ?_⟩
  · intro i j hij
    rw [hPX, hPX]
    exact hZo i j hij
  · intro i
    rw [hPX]
    exact hZd i

end Formalism.L2.SG.Pf.NcS.IntWittAlg
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWitt

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
  Matrix Formalism.L2.SG.Pf.NcS.KfOrbPf Formalism.L2.SG.Pf.NcS.IntWittAlg
open scoped TensorProduct

section Main

theorem sigR_inclR' {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem hform_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Formalism.UG.hform (sigR R σ) (JR R J) (fun i => inclR R (x i)) (fun i => inclR R (y i)) =
      inclR R (Formalism.UG.hform (σ : E →+* E) J x y) := by

  simp only [Formalism.UG.hform, map_sum, map_mul, JR, Matrix.map_apply, sigR_inclR']
  rfl

theorem intWittAE_of (hA : AlgWitt) (hD : HermDiag) (hL : LamAE) : LocSBPf.IntWittAE := by
  intro F E _ _ _ _ _ σ n J a X0 Λ hCM hJ hT hLat d b
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨L, hLL, rfl⟩ := hLat
  have hσ : ∀ z, σ (σ z) = z := PI.VolStabS.sigma_invol σ hCM.2.2.2
  have hJh : Formalism.UG.IsHerm (σ : E →+* E) J := by
    unfold Formalism.UG.IsHerm Formalism.UG.cT
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    exact hJ.1 i j
  obtain ⟨P, Q, hQP, hPo, hPd⟩ := hD E (σ : E →+* E) hσ two_ne_zero n J hJh a X0 hT
  set Z0 : Fin a → Fin n → E := fun i => ∑ l, P i l • X0 l with hZ0
  have hZ0e : ∀ i, Z0 i = ∑ l, P i l • X0 l := fun i => rfl
  have hX0e : ∀ c, X0 c = ∑ l, Q c l • Z0 l := fun c => by
    funext k
    simp only [hZ0, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hm : ∀ m, ∑ l, Q c l * (P l m * X0 m k) = (if c = m then 1 else 0) * X0 m k := by
      intro m
      simp_rw [← mul_assoc, ← Finset.sum_mul]
      rw [← Matrix.mul_apply, hQP, Matrix.one_apply]
    simp_rw [hm]
    simp
  let δ : Fin a → E := fun i => Formalism.UG.hform (σ : E →+* E) J (Z0 i) (Z0 i)
  have hδσ : ∀ i, σ (δ i) = δ i := fun i => hform_conj (σ : E →+* E) J hσ hJh _ _
  have hJi : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.2 hJ.2)
  filter_upwards [ev_latLoc_std L hLL,
    eventually_all.2 fun k => ev_oev (F := F) (b k),
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (J i j),
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (J⁻¹ i j),
    eventually_all.2 fun i => ev_oev (F := F) (δ i),
    eventually_all.2 fun i => ev_oev (F := F) (δ i)⁻¹,
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (P i j),
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (Z0 i j),
    eventually_all.2 fun i => hL F E σ hCM (δ i) (hδσ i) (hPd i)]
    with v hstd hbv hJv hJiv hδv hδiv hPv hZv hlam
  intro X hX hgram
  let O := oevRing (E := E) v
  have hXO : ∀ c k, X c k ∈ O := by
    intro c k
    show X c k ∈ OEv (E := E) v
    rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr (X c k)]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    exact oev_smul' v (hX c k l) (hbv l)
  let s := sigR (Fv F v) σ
  have hs : ∀ z, s (s z) = z := PI.VolStabS.sigR_invol (Fv F v) σ hσ
  have hsO : ∀ z ∈ O, s z ∈ O := by
    intro z hz
    exact oev_sigR v σ hz
  let Jv := JR (F := F) (Fv F v) J
  let Jv' := JR (F := F) (Fv F v) J⁻¹
  have hJJ : Jv' * Jv = 1 := by
    show J⁻¹.map (inclR (F := F) (Fv F v)) * J.map (inclR (F := F) (Fv F v)) = 1
    rw [← Matrix.map_mul, hJi, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJvh : Formalism.UG.IsHerm s Jv := by
    unfold Formalism.UG.IsHerm Formalism.UG.cT
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Jv, JR, s, sigR_inclR']
    rw [hJ.1 i j]
  let y : Fin a → Fin n → Fv F v ⊗[F] E := fun i k => inclR (F := F) (Fv F v) (Z0 i k)
  let x : Fin a → Fin n → Fv F v ⊗[F] E := fun i => ∑ l, inclR (F := F) (Fv F v) (P i l) • X l
  have hxO : ∀ i k, x i k ∈ O := by
    intro i k
    simp only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact O.sum_mem fun l _ => O.mul_mem (hPv i l) (hXO l k)
  have hyy : ∀ i j, Formalism.UG.hform s Jv (y i) (y j) = if i = j then inclR (F := F) (Fv F v) (δ i) else 0 := by
    intro i j
    rw [show Formalism.UG.hform s Jv (y i) (y j) = inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (Z0 i) (Z0 j)) from
      hform_inclR _ σ J _ _]
    split_ifs with h
    · subst h; rfl
    · rw [hPo i j h, map_zero]
  have hXX : ∀ l m, Formalism.UG.hform s Jv (X l) (X m) =
      inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (X0 l) (X0 m)) := by
    intro l m
    exact congrFun (congrFun hgram l) m
  have hxx : ∀ i j, Formalism.UG.hform s Jv (x i) (x j) = if i = j then inclR (F := F) (Fv F v) (δ i) else 0 := by
    intro i j
    have e1 : Formalism.UG.hform s Jv (x i) (x j) = inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (Z0 i) (Z0 j)) := by
      calc Formalism.UG.hform s Jv (x i) (x j)
          = ∑ l, inclR (F := F) (Fv F v) (σ (P i l)) * ∑ m, inclR (F := F) (Fv F v) (P j m) *
              inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (X0 l) (X0 m)) := by
            simp only [x]
            rw [hform_sum_left]
            simp_rw [hform_sum_right, hXX, s, sigR_inclR']
        _ = _ := by
            rw [hZ0e i, hZ0e j, hform_sum_left]
            simp_rw [hform_sum_right]

            simp only [map_sum, map_mul]
            rfl
    rw [e1]
    split_ifs with h
    · subst h; rfl
    · rw [hPo i j h, map_zero]
  obtain ⟨g, hg, hgO, hgiO, hgy⟩ := hA (Fv F v ⊗[F] E) s O hs hsO n Jv Jv' hJvh hJJ hJv hJiv a
    (fun i => inclR (F := F) (Fv F v) (δ i)) (fun i => inclR (F := F) (Fv F v) (δ i)⁻¹) hδv hδiv
    (fun i => by rw [← map_mul, mul_inv_cancel₀ (hPd i), map_one])
    hlam x y hxO hZv hxx hyy
  refine ⟨(⟨g, hg⟩ : HR (Fv F v) σ J), ?_, ?_⟩
  · show ∀ w, w ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔
      (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ w ∈ latLoc (E := E) v (L : Set (Fin n → E))
    rw [hstd]
    intro w
    constructor
    · intro hw
      exact mem_std_of_oev v _ fun i => mulVec_mem O _ hgO w (fun k => mem_oev_of_std v w hw k) i
    · intro hw
      have e : w = ((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ
          ((g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ w) := by
        rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      rw [e]
      exact mem_std_of_oev v _ fun i => mulVec_mem O _ hgiO _ (fun k => mem_oev_of_std v _ hw k) i
  · funext c
    show (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ ratTup (F := F) (Fv F v) X0 c = X c
    have e1 : ratTup (F := F) (Fv F v) X0 c = ∑ l, inclR (F := F) (Fv F v) (Q c l) • y l := by
      funext k
      simp only [ratTup, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, y]
      rw [hX0e c]

      simp [Finset.sum_apply, map_sum, map_mul]
    rw [e1, mulVec_sum]
    simp_rw [mulVec_smul, hgy]
    funext k
    simp only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hm : ∀ m, ∑ l, inclR (F := F) (Fv F v) (Q c l) * (inclR (F := F) (Fv F v) (P l m) * X m k) =
        (if c = m then 1 else 0) * X m k := by
      intro m

      simp_rw [← mul_assoc, ← Finset.sum_mul, ← map_mul, ← map_sum]
      rw [← Matrix.mul_apply, hQP, Matrix.one_apply]
      split_ifs <;> simp
    simp_rw [hm]
    simp

end Main

theorem integral_witt_almost_everywhere : Formalism.L2.SG.Pf.NcS.LocSBPf.IntWittAE :=
  intWittAE_of IntWittAlg.algWitt IntWittAlg.hermDiag lamAE

end Formalism.L2.SG.Pf.NcS.IntWittPf
end
end
end
