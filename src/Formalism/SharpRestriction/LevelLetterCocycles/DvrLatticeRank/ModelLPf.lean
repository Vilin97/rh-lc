module

public import Formalism.SharpRestriction.LevelLetterCocycles.ModelKStep
public import Formalism.SharpRestriction.LevelLetterCocycles.DivisibilityInvariantMulLinear
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfD
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfH
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfF
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfB
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfE
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfG
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3upPfFilCAnti
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
import Mathlib.Tactic.Linter.Style
public import Formalism.SharpRestriction.LevelLetterCocycles.LamPS
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfL
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfI

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLI

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem expS_neg (ζ : LL) {m : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T) {i : ℤ} (hi : i < 0) :
    expS W T c ζ a y i = 0 := by
  simp [expS, serC, if_neg (show ¬ (0 ≤ i) by omega)]

theorem ind_fil (τ : K →ₐ[Qp] LL) (U : PowerSeries LL) (hU : PowerSeries.constantCoeff U ≠ 0)
    {g : ℤ → T.V ⊗[Qp] BdR} {m₀ : ℤ} (hg : MLG.Bdd g m₀)
    (hH : ∀ j, serMul U g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j)) :
    ∀ j, g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
  have key : ∀ N : ℕ, ∀ j, j < m₀ + N → g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
    intro N
    induction N with
    | zero => intro j hj; rw [hg j (by omega)]; exact Submodule.zero_mem _
    | succ N ih =>
      intro j hj
      by_cases hjN : j < m₀ + N
      · exact ih j hjN
      · have hj' : j = m₀ + N := by push_cast at hj; omega
        have hs := hH j
        rw [MLG.serMul_eq_sum U hg j ((j - m₀).toNat + 1) le_rfl, Finset.sum_range_succ'] at hs
        have hrest : ∑ k ∈ Finset.range (j - m₀).toNat, PowerSeries.coeff (k + 1) U • g (j - ((k + 1 : ℕ) : ℤ)) ∈
            Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
          refine Submodule.sum_mem _ (fun k hk => Submodule.smul_mem _ _ ?_)
          rw [Finset.mem_range] at hk
          exact u3upPf_FilC_anti (PD := PD) T τ (by push_cast; omega) (ih _ (by push_cast; omega))
        have h0 := Submodule.sub_mem _ hs hrest
        rw [add_sub_cancel_left, PowerSeries.coeff_zero_eq_constantCoeff_apply, Nat.cast_zero, sub_zero] at h0
        exact (Submodule.smul_mem_iff _ hU).1 h0
  intro j
  exact key ((j - m₀).toNat + 1) j (by omega)

end Generic

end Formalism.MainNotions.N.Ln34.MLI

end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfJ

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLJ

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem local_form (hwd : MLF.WD W T Pt π' c) {u₀ : LetA O n} (hu₀ : u₀ ∈ W.AΔ)
    (hΛ : u₀ * W.γA W.gamK (Eπ ^ h') = Eπ ^ h') (hlet : W.γA W.gamK (letE c : LetA O n) = letE c)
    (u : LL) (hu : u ≠ 0) (hu1 : ∀ i : ℤ, i ≠ 0 → u ^ i ≠ 1)
    (hlev : ∀ τ ζ, Pt c ζ τ → ∀ a, W.lev c ζ (W.γA W.gamK a) = PowerSeries.rescale u (W.lev c ζ a))
    (hsimp : ∀ τ ζ, Pt c ζ τ → ∃ U : PowerSeries LL, W.lev c ζ (Eπ ^ h') = PowerSeries.X ^ h' * U ∧
      PowerSeries.constantCoeff U ≠ 0)
    {x : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤)
    (hγ : γLA W T π' c x - x ∈ NL W T Pt π' Eπ h' c) :
    ∀ τ ζ, Pt c ζ τ → ∀ f, ExpL W T π' Eπ h' c ζ x f → ∀ i : ℤ, i ≠ 0 →
      f i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-i) := by
  intro τ ζ hpt f hf i hi
  obtain ⟨⟨m₀, hf0⟩, m, a, y, hr, hfe⟩ := hf
  have hfb : MLG.Bdd f m₀ := hf0

  have hrγ := MLH.rep_γ W T π' Eπ h' c hu₀ hΛ hlet hr
  have hrn := MLE.rep_smul W T π' Eπ h' c hr (W.AΔ.algebraMap_mem (-1 : O))
  rw [← MLE.smul_eq_smulLA, neg_one_smul] at hrn
  have hra := MLE.rep_append W T π' Eπ h' c hrγ hrn
  rw [← sub_eq_add_neg] at hra
  have hgood := MLF.good_all W T Pt π' Eπ h' c hwd hγ hra τ ζ hpt
  rw [MLE.expS_append] at hgood
  set e := expS W T c ζ (fun j => (a j : LetA O n)) y with he
  have heb : MLG.Bdd e 0 := fun j hj => MLI.expS_neg W T c ζ _ y hj

  have hneg : expS W T c ζ (fun j => ((⟨algebraMap O (LetA O n) (-1) * a j,
      W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (a j).2⟩ : ↥W.AΔ) : LetA O n)) y = -e := by
    show expS W T c ζ (fun j => algebraMap O (LetA O n) (-1) * (a j : LetA O n)) y = -e
    rw [MLF.expS_alg_mul, map_neg, map_one, neg_one_smul]
  obtain ⟨U, hU, hU0⟩ := hsimp τ ζ hpt
  have hfu : MLG.Bdd (fun s => u ^ s • f s) m₀ := fun s hs => by simp only [hfb s hs, smul_zero]
  have hγpart : ∀ j, expS W T c ζ (fun k => ((⟨u₀ * W.γA W.gamK (a k), W.AΔ.mul_mem hu₀
      (MLH.γA_mem_AΔ W (a k).2)⟩ : ↥W.AΔ) : LetA O n)) y j =
      serMul (W.lev c ζ (Eπ ^ h')) (fun s => u ^ s • f s) j := by
    intro j
    show expS W T c ζ (fun k => u₀ * W.γA W.gamK (a k)) y j = _
    have hLdec : W.lev c ζ (Eπ ^ h') = W.lev c ζ u₀ * PowerSeries.rescale u (W.lev c ζ (Eπ ^ h')) := by
      rw [← hlev τ ζ hpt, ← map_mul, hΛ]
    rw [MLB.expS_mul, hLdec, ← MLG.serMul_serMul _ _ hfu]
    have hin : serMul (PowerSeries.rescale u (W.lev c ζ (Eπ ^ h'))) (fun s => u ^ s • f s) =
        fun s => u ^ s • e s := by
      funext s
      rw [← MLG.serMul_rescale u hu, hfe s]
    rw [hin, MLG.serMul_eq_sum (m₀ := 0) _ (fun s hs => by simp only [heb s hs, smul_zero]) j (j.toNat + 1) (by omega)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [MLH.expS_γ W T c ζ u (hlev τ ζ hpt)]
    congr 1
    by_cases hjk : 0 ≤ j - (k : ℤ)
    · rw [← zpow_natCast, Int.toNat_of_nonneg hjk]
    · rw [MLI.expS_neg W T c ζ _ y (by omega), heb _ (by omega), smul_zero, smul_zero]

  set g : ℤ → T.V ⊗[Qp] BdR := fun s => u ^ s • f s - f s with hgdef
  have hgb : MLG.Bdd g m₀ := fun s hs => by simp [hgdef, hfb s hs]
  have hGg : ∀ j, serMul (W.lev c ζ (Eπ ^ h')) g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (h' - j) := by
    intro j
    have h1 := hgood j
    rw [Pi.add_apply, hγpart j, hneg, Pi.neg_apply, ← hfe j, ← sub_eq_add_neg] at h1
    convert h1 using 1
    rw [MLG.serMul_eq_sum _ hgb j _ le_rfl, MLG.serMul_eq_sum _ hfu j _ le_rfl,
      MLG.serMul_eq_sum _ hfb j _ le_rfl, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hgdef, smul_sub]
  have hH : ∀ j, serMul U g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
    intro j
    have h1 := hGg (j + h')
    rw [hU, ← MLG.serMul_serMul _ _ hgb, MLG.serMul_X_pow, add_sub_cancel_right] at h1
    convert h1 using 2
    ring
  have hgi := MLI.ind_fil T τ U hU0 hgb hH i
  have e1 : g i = (u ^ i - 1) • f i := by rw [hgdef, sub_smul, one_smul]
  rw [e1] at hgi
  exact (Submodule.smul_mem_iff _ (sub_ne_zero.2 (hu1 i hi))).1 hgi

end Generic

end Formalism.MainNotions.N.Ln34.MLJ

end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfK

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLK

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module



theorem lev_Eat_simple (D : D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hr : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) (c : ZMod (finrank ℚ_[l] ↥(K0 K)))
    (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) :
    ∃ U : PowerSeries ↥LL.1, ((HW l).W K 1 LL hG).lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') = PowerSeries.X * U ∧
      PowerSeries.constantCoeff U ≠ 0 := by
  obtain ⟨τs, hIs, -⟩ := hpt
  obtain ⟨-, hIs2⟩ := hIs
  unfold Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations at hr
  obtain ⟨-, -, -, -, ⟨w, hw⟩, -, -, -⟩ := hr
  generalize (HW l).W K 1 LL hG = W at hw ⊢

  have hz : (D.loc l).ζQ 1 ^ l = 1 := by
    have h := (D.loc l).ζQ_succ 0
    rw [(D.loc l).ζQ_zero] at h
    simpa using h
  have hmem : (D.loc l).ζQ 1 ∈ Ks K 1 := by
    show (D.loc l).ζQ 1 ∈ K0 K ⊔ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1}
    exact SetLike.le_def.mp le_sup_right (IntermediateField.subset_adjoin ℚ_[l] _ (by simpa using hz))
  have hζ : τs ⟨_, hmem⟩ = ζ := hIs2 ⟨_, hmem⟩ rfl
  have hζl : ζ ^ l = 1 := by
    have h1 : (⟨_, hmem⟩ : ↥(Ks K 1)) ^ l = 1 := Subtype.ext (by simpa using hz)
    rw [← hζ, ← map_pow, h1, map_one]
  have hne : ζ ≠ 1 := by
    intro h1
    have h2 : (⟨_, hmem⟩ : ↥(Ks K 1)) = 1 :=
      RingHom.injective (τs : ↥(Ks K 1) →+* ↥LL.1) (by simp [hζ, h1])
    exact (D.loc l).ζQ_one (by simpa using congrArg Subtype.val h2)
  have hprim : IsPrimitiveRoot ζ l := by
    have h := IsPrimitiveRoot.orderOf ζ
    rwa [orderOf_eq_prime hζl hne] at h
  have hl0 : ((l : ℕ) : ↥LL.1) ≠ 0 := by
    intro h
    have h' := (D.loc l).v_l LL
    rw [h, AddValuation.map_zero] at h'
    simp at h'

  obtain ⟨F, hF0, hFd, hFπ⟩ :=
    W.lev_π c ζ ⟨1, by rw [(D.loc l).PD_p K, pow_one]; exact hprim⟩
  obtain ⟨F1, hF1⟩ : PowerSeries.X ∣ F - 1 := by
    rw [PowerSeries.X_dvd_iff, map_sub, hF0, map_one, sub_self]
  have hF1c : PowerSeries.constantCoeff F1 = 1 := by
    have hd := congrArg (fun f : PowerSeries ↥LL.1 => PowerSeries.constantCoeff (PowerSeries.derivative f)) hF1
    simp only [map_sub, Derivation.map_one_eq_zero, sub_zero, hFd, hF0, Derivation.leibniz,
      PowerSeries.derivative_X, smul_eq_mul, map_add, map_mul, map_one, PowerSeries.constantCoeff_X,
      zero_mul, zero_add, mul_one] at hd
    exact hd.symm

  have hq : (letπ : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) * W.q =
      (1 + letπ) ^ ((D.loc l).PD K).p - 1 := by
    funext i
    exact W.q₀_def
  have hl1 : W.lev c ζ 1 = 1 := map_one (W.lev c ζ)
  have hadd : W.lev c ζ (1 + letπ) = 1 + W.lev c ζ letπ := by
    rw [← hl1]
    exact (W.lev c ζ).map_add 1 letπ
  have hlq := congrArg (W.lev c ζ) hq
  rw [map_mul (W.lev c ζ), map_sub (W.lev c ζ), map_pow (W.lev c ζ), hadd, hl1, hFπ, (D.loc l).PD_p K, mul_pow, ← map_pow PowerSeries.C ζ l, hζl,
    map_one PowerSeries.C, one_mul, ← mul_geom_sum, hF1, hw, map_mul (W.lev c ζ)] at hlq
  have hy0 : PowerSeries.constantCoeff (W.lev c ζ letπ) ≠ 0 := by
    have h := congrArg PowerSeries.constantCoeff hFπ
    rw [map_add (f := _), map_one, map_mul, PowerSeries.constantCoeff_C, hF0, mul_one] at h
    have h' : PowerSeries.constantCoeff (W.lev c ζ letπ) = ζ - 1 := by linear_combination h
    rw [h']
    exact sub_ne_zero.mpr hne
  obtain ⟨u, hu⟩ : IsUnit (W.lev c ζ letπ * W.lev c ζ ↑w) :=
    (PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hy0)).mul
      (w.isUnit.map (W.lev c ζ))
  rw [← mul_assoc, ← hu] at hlq
  refine ⟨↑u⁻¹ * (F1 * ∑ i ∈ Finset.range l, F ^ i), ?_, ?_⟩
  · calc _ = ↑u⁻¹ * (↑u * W.lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [hlq]; ring
  · rw [map_mul]
    refine mul_ne_zero ((u⁻¹).isUnit.map PowerSeries.constantCoeff).ne_zero ?_

    rw [map_mul, hF1c, one_mul, map_sum]
    simpa [hF0] using hl0

end Formalism.MainNotions.N.Ln34.MLK
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPf

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem modell_pf : ModelLStep := by
  unfold ModelLStep modelLR recU
  intro D HW F Cm CA CB CK hA l _ hl K LL hG π' E hr h' hh' T hT hJ c
  obtain ⟨u₀, hu₀, hΛ⟩ := MLL.exists_mul_gamma_Eat_pow_eq_Eat_pow D HW F Cm CA CB CK hA l hl K LL hG π' E hr h'
  obtain ⟨hu, hu1⟩ := MLL.rec_u D HW l hl K LL hG
  have hwd := MLL.rec_WD D HW F Cm CA CB CK hA l hl K LL hG π' E hr T hT c
  have hlet := Formalism.MainNotions.ArcLiftingSetup.γA_letE ((HW l).W K 1 LL hG) ((HW l).W K 1 LL hG).gamK c
  have hlev := fun τ ζ (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) a =>
    MLL.rec_lev D HW F Cm l hl K LL hG c τ ζ hpt a
  unfold ModelL
  refine ⟨MLF.nl_le _ _ _ _ _ _ _, fun x hx => MLH.nl_γ _ _ _ _ _ _ _ hu₀ hΛ hlet _ hlev hx,
    fun a ha x hx => MLF.nl_smulA _ _ _ _ _ _ _ ha hx,
    MLD.model_lattice_filtration D HW F Cm CA CB CK hA l hl K LL hG π' E hr h' hh' T hT hJ c,
    fun x hx k hk => MLF.nl_sat _ _ _ _ _ _ _ hwd ?_ hx k hk,
    MLD.model_lattice_power D HW F Cm CA CB CK hA l hl K LL hG π' E hr h' hh' T hT hJ c,
    fun x hx hγ => MLJ.local_form _ _ _ _ _ _ _ hwd hu₀ hΛ hlet _ hu hu1 hlev ?_ hx hγ⟩
  · rw [map_natCast]
    exact Formalism.MainNotions.LiftingTheory.tr_pLL_ne ((HW l).W K 1 LL hG)
  · intro τ ζ hpt
    obtain ⟨U, hU, hU0⟩ := MLK.lev_Eat_simple D HW l hl K LL hG π' E hr c ζ τ hpt
    refine ⟨U ^ h', ?_, ?_⟩
    · rw [map_pow, hU, mul_pow]
    · rw [map_pow]
      exact pow_ne_zero _ hU0

end Formalism.MainNotions.N.Ln34

end
end
end
