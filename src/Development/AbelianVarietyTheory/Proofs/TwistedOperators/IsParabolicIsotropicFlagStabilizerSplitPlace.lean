module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlAdaptedBasisMonotoneSubspaceChainStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitInclMemExtSubIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIsotropicFlagParabolicIffSplitPlaceChain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StdMaxParabolicRadicalLeBlockUnipotentRadical
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIsotropicFlagParabolicIffSplitPlaceChainStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.mem_isotropicFlagParabolic_iff_splitPlaceChain : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)} (hc : Formalism.BasicNotions.CMData F E), IsCMExt F E hc.sig →
    IsHermND hc.sig V.gram → ∀ (τ : E →ₐ[F] Fv F v) (𝔉 : GlobalTheory.Cusp.IsoFlag V) (g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v),
    g ∈ 𝔉.par hc (Fv F v) ↔ ∀ j, ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j,
      ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v)) *ᵥ u ∈
        GlobalTheory.SplitFlag.flagChain 𝔉 τ j := by
  first | exact @GlobalTheory.SplitFlag.mem_par_iff_flagChain | exact GlobalTheory.SplitFlag.mem_par_iff_flagChain | (intros; apply GlobalTheory.SplitFlag.mem_par_iff_flagChain <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIsotropicFlagUnipotentIffSplitChainTrivial

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SplitFlag

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)}

theorem splitVec_sub' (τ : E →ₐ[F] Fv F v) (y z : Fin V.rank → Fv F v ⊗[F] E) :
    splitVec τ (y - z) = splitVec τ y - splitVec τ z := funext fun _ => map_sub _ _ _

variable (hc : Formalism.BasicNotions.CMData F E) (τ : E →ₐ[F] Fv F v)

theorem wPart_sub_of_mem_trivOn {A B : Submodule E V.V} {g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v}
    (hg : g ∈ trivOn hc V (Fv F v) A B) {u : Fin V.rank → Fv F v} (hu : u ∈ wPart τ B) :
    (splitHom hc.sig V.gram τ g).1 *ᵥ u - u ∈ wPart τ A := by
  obtain ⟨y, hy, rfl⟩ := hu
  refine ⟨act hc V g y - y, hg.2 y hy, ?_⟩
  change splitVec τ ((matHom _ hc.sig V.gram g).1 *ᵥ y - y) = _
  rw [splitVec_sub', splitVec_matHom_mulVec]

variable (h : IsCMExt F E hc.sig) (hJ : IsHermND hc.sig V.gram)


include h hJ in
theorem mem_trivOn_of_wPart {A B : Submodule E V.V} (hAB : A ≤ B) {g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v}
    (h1 : ∀ u ∈ wPart τ B, (splitHom hc.sig V.gram τ g).1 *ᵥ u - u ∈ wPart τ A)
    (h2 : ∀ u ∈ wPart τ (perp V A), (splitHom hc.sig V.gram τ g).1 *ᵥ u - u ∈ wPart τ (perp V B))
    (h3 : ∀ u ∈ wPart τ (perp V A), ∃ u₀ ∈ wPart τ (perp V A), (splitHom hc.sig V.gram τ g).1 *ᵥ u₀ = u) :
    g ∈ trivOn hc V (Fv F v) A B := by
  refine (mem_trivOn_iff_maps hAB).2 fun y hy => ?_
  rw [mem_extSub_iff_split hc h τ] at hy ⊢
  change splitVec τ ((matHom _ hc.sig V.gram g).1 *ᵥ y - y) ∈ _ ∧
    splitVec (τ.comp hc.sig) ((matHom _ hc.sig V.gram g).1 *ᵥ y - y) ∈ _
  rw [splitVec_sub', splitVec_sub', splitVec_matHom_mulVec, splitVec_matHom_mulVec]
  refine ⟨h1 _ hy.1, ?_⟩
  rw [mem_wPart_comp_iff hc h hJ τ]
  intro u hu
  obtain ⟨u₀, hu₀, rfl⟩ := h3 u hu
  have e := (mem_wPart_comp_iff hc h hJ τ).1 hy.2 _ (h2 u₀ hu₀)
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_eq_zero] at e
  rw [sub_dotProduct, pairing_splitHom, e, sub_self]

variable (𝔉 : IsoFlag V)

theorem flagChain_step_lo (i : Fin 𝔉.k) (j : Fin (2 * 𝔉.k + 1)) (hj : (j : ℕ) = i) :
    flagChain 𝔉 τ j.succ = wPart τ (𝔉.X i.succ) ∧ flagChain 𝔉 τ j.castSucc = wPart τ (𝔉.X i.castSucc) := by
  have := i.2
  refine ⟨?_, ?_⟩
  · rw [flagChain_of_le 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (𝔉.X a)) (Fin.ext (by simp <;> omega))
  · rw [flagChain_of_le 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (𝔉.X a)) (Fin.ext (by simp <;> omega))

theorem flagChain_step_mid (j : Fin (2 * 𝔉.k + 1)) (hj : (j : ℕ) = 𝔉.k) :
    flagChain 𝔉 τ j.succ = wPart τ (perp V 𝔉.top) ∧ flagChain 𝔉 τ j.castSucc = wPart τ 𝔉.top := by
  refine ⟨?_, ?_⟩
  · rw [flagChain_of_lt 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (perp V (𝔉.X a))) (Fin.ext (by simp <;> omega))
  · rw [flagChain_of_le 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (𝔉.X a)) (Fin.ext (by simp <;> omega))

theorem flagChain_step_hi (i : Fin 𝔉.k) (j : Fin (2 * 𝔉.k + 1)) (hj : (j : ℕ) + i = 2 * 𝔉.k) :
    flagChain 𝔉 τ j.succ = wPart τ (perp V (𝔉.X i.castSucc)) ∧
      flagChain 𝔉 τ j.castSucc = wPart τ (perp V (𝔉.X i.succ)) := by
  have := i.2
  refine ⟨?_, ?_⟩
  · rw [flagChain_of_lt 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (perp V (𝔉.X a))) (Fin.ext (by simp <;> omega))
  · rw [flagChain_of_lt 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (perp V (𝔉.X a))) (Fin.ext (by simp <;> omega))

end GlobalTheory.SplitFlag


open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act) in
theorem GlobalTheory.SplitFlag.mem_unip_iff_flagChain : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)} (hc : Formalism.BasicNotions.CMData F E), IsCMExt F E hc.sig →
    IsHermND hc.sig V.gram → ∀ (τ : E →ₐ[F] Fv F v) (𝔉 : GlobalTheory.Cusp.IsoFlag V) (g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v),
    g ∈ 𝔉.unip hc (Fv F v) ↔ ∀ j : Fin (2 * 𝔉.k + 1), ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j.succ,
      ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v)) *ᵥ u - u ∈
        GlobalTheory.SplitFlag.flagChain 𝔉 τ j.castSucc := by
  intro F E _ _ _ _ _ _ V v hc h hJ τ 𝔉 g
  constructor
  · intro hg j u hu
    simp only [IsoFlag.unip, Subgroup.mem_inf, Subgroup.mem_iInf] at hg
    obtain ⟨⟨hlo, hmid⟩, hhi⟩ := hg
    have := j.2
    rcases lt_trichotomy (j : ℕ) 𝔉.k with hj | hj | hj
    · obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_lo τ 𝔉 ⟨j, hj⟩ j rfl
      rw [e1] at hu; rw [e2]; exact GlobalTheory.SplitFlag.wPart_sub_of_mem_trivOn hc τ (hlo _) hu
    · obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_mid τ 𝔉 j hj
      rw [e1] at hu; rw [e2]; exact GlobalTheory.SplitFlag.wPart_sub_of_mem_trivOn hc τ hmid hu
    · obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_hi τ 𝔉 ⟨2 * 𝔉.k - j, by omega⟩ j
        (show (j : ℕ) + (2 * 𝔉.k - j) = 2 * 𝔉.k by omega)
      rw [e1] at hu; rw [e2]; exact GlobalTheory.SplitFlag.wPart_sub_of_mem_trivOn hc τ (hhi _) hu
  · intro H
    have hstab : ∀ j : Fin (2 * 𝔉.k + 2), ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j,
        (splitHom hc.sig V.gram τ g).1 *ᵥ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j := by
      intro j u hu
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · rw [GlobalTheory.SplitFlag.flagChain_zero, Submodule.mem_bot] at hu ⊢
        rw [hu, Matrix.mulVec_zero]
      · have := GlobalTheory.SplitFlag.flagChain_mono 𝔉 τ (Fin.castSucc_le_succ j') (H j' u hu)
        simpa using add_mem this hu
    have hsurj : ∀ j : Fin (2 * 𝔉.k + 2), ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j,
        ∃ u₀ ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j, (splitHom hc.sig V.gram τ g).1 *ᵥ u₀ = u :=
      fun j u hu => GlobalTheory.SplitFlag.exists_mulVec_eq_of_maps _ _ (hstab j) u hu
    rw [IsoFlag.mem_unip]
    refine ⟨fun i => ?_, ?_⟩
    · have := i.2
      obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_lo τ 𝔉 i ⟨i, by omega⟩ rfl
      obtain ⟨e3, e4⟩ := GlobalTheory.SplitFlag.flagChain_step_hi τ 𝔉 i ⟨2 * 𝔉.k - i, by omega⟩
        (show 2 * 𝔉.k - (i : ℕ) + i = 2 * 𝔉.k by omega)
      refine GlobalTheory.SplitFlag.mem_trivOn_of_wPart hc τ h hJ (𝔉.le_succ i) ?_ ?_ ?_
      · rw [← e1, ← e2]; exact H _
      · rw [← e3, ← e4]; exact H _
      · rw [← e3]; exact hsurj _
    · obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_mid τ 𝔉 ⟨𝔉.k, by omega⟩ rfl
      refine GlobalTheory.SplitFlag.mem_trivOn_of_wPart hc τ h hJ 𝔉.iso ?_ ?_ ?_
      · rw [← e1, ← e2]; exact H _
      · rw [GlobalTheory.SplitFlag.perp_perp, ← e1, ← e2]; exact H _
      · rw [← e1]; exact hsurj _
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIsotropicFlagUnipotentIffSplitChainTrivialStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.mem_isotropic_flag_unipotent_iff_split_chain_trivial : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)} (hc : Formalism.BasicNotions.CMData F E), IsCMExt F E hc.sig →
    IsHermND hc.sig V.gram → ∀ (τ : E →ₐ[F] Fv F v) (𝔉 : GlobalTheory.Cusp.IsoFlag V) (g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v),
    g ∈ 𝔉.unip hc (Fv F v) ↔ ∀ j : Fin (2 * 𝔉.k + 1), ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j.succ,
      ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v)) *ᵥ u - u ∈
        GlobalTheory.SplitFlag.flagChain 𝔉 τ j.castSucc := by
  first | exact @GlobalTheory.SplitFlag.mem_unip_iff_flagChain | exact GlobalTheory.SplitFlag.mem_unip_iff_flagChain | (intros; apply GlobalTheory.SplitFlag.mem_unip_iff_flagChain <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedStandardChainStabilizerRadical

section

@[expose] public section

open scoped Matrix

namespace GlobalTheory.StdChainStab

open Matrix

variable {K : Type} [Field K] {n m : ℕ}

def lowVec (b : Fin n → Fin m) (j : ℕ) (w : Fin n → K) : Prop :=
  ∀ i : Fin n, j ≤ ((b i : Fin m) : ℕ) → w i = 0

theorem lowVec_single (b : Fin n → Fin m) (c : Fin n) :
    lowVec b ((b c : ℕ) + 1) (Pi.single c (1 : K)) := by
  intro i hi
  have : i ≠ c := by rintro rfl; omega
  simp [Pi.single_apply, this]

theorem mulVec_single_apply (z : Matrix (Fin n) (Fin n) K) (i c : Fin n) :
    (z *ᵥ Pi.single c (1 : K)) i = z i c := by
  simp [Matrix.mulVec_single_one]

theorem stab_iff (b : Fin n → Fin m) (z : Matrix (Fin n) (Fin n) K) :
    (∀ j : Fin (m + 1), ∀ w, lowVec b j w → lowVec b j (z *ᵥ w)) ↔
      ∀ i c, b c < b i → z i c = 0 := by
  constructor
  · intro H i c hic
    have h1 := H ⟨(b c : ℕ) + 1, by omega⟩ _ (lowVec_single b c) i (by simp; exact hic)
    rwa [mulVec_single_apply] at h1
  · intro H j w hw i hi
    simp only [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : (j : ℕ) ≤ (b c : ℕ)
    · rw [hw c hc, mul_zero]
    · rw [H i c (by rw [Fin.lt_iff_val_lt_val]; omega), zero_mul]

theorem rad_iff (b : Fin n → Fin m) (z : Matrix (Fin n) (Fin n) K) :
    (∀ j : Fin m, ∀ w, lowVec b (j.succ : ℕ) w → lowVec b (j.castSucc : ℕ) (z *ᵥ w - w)) ↔
      ∀ i c, ¬ b i < b c → z i c = (1 : Matrix (Fin n) (Fin n) K) i c := by
  constructor
  · intro H i c hic
    have h1 := H (b c) _ (by simpa using lowVec_single (K := K) b c) i
      (by simp; exact (not_lt.1 hic))
    rw [Pi.sub_apply, mulVec_single_apply, sub_eq_zero] at h1
    simpa [Pi.single_apply, Matrix.one_apply, eq_comm] using h1
  · intro H j w hw i hi
    have e : z *ᵥ w - w = (z - 1) *ᵥ w := by rw [sub_mulVec, one_mulVec]
    rw [e]
    simp only [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : (j : ℕ) + 1 ≤ (b c : ℕ)
    · rw [hw c (by simpa using hc), mul_zero]
    · simp only [Fin.coe_castSucc] at hi
      rw [Matrix.sub_apply, H i c (by rw [Fin.lt_iff_val_lt_val]; omega), sub_self, zero_mul]

theorem transport (Gm Gi X : Matrix (Fin n) (Fin n) K) (h1 : Gi * Gm = 1) (h2 : Gm * Gi = 1)
    (P : (Fin n → K) → Prop) (Q : (Fin n → K) → (Fin n → K) → Prop) :
    (∀ y, P (Gi *ᵥ y) → Q (Gi *ᵥ y) (Gi *ᵥ (X *ᵥ y))) ↔ ∀ w, P w → Q w ((Gi * X * Gm) *ᵥ w) := by
  constructor
  · intro H w hw
    have hw' : Gi *ᵥ (Gm *ᵥ w) = w := by rw [mulVec_mulVec, h1, one_mulVec]
    have := H (Gm *ᵥ w) (by rw [hw']; exact hw)
    rw [hw'] at this
    simpa [mulVec_mulVec, Matrix.mul_assoc] using this
  · intro H y hy
    have := H _ hy
    simpa [mulVec_mulVec, Matrix.mul_assoc, h2] using this

theorem stdChain_stab_rad : ∀ {K : Type} [Field K] {n m : ℕ} (Y : Fin (m + 1) → Submodule K (Fin n → K)) (d : Fin m → ℕ) (h : ∑ j, d j = n)
    (g : GL (Fin n) K), (∀ (j : Fin (m + 1)) (y : Fin n → K),
      y ∈ Y j ↔ ∀ i : Fin n, (j : ℕ) ≤ ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d h) i : Fin m) : ℕ) →
        (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) i = 0) →
    (∀ x : GL (Fin n) K, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy g (GlobalTheory.SmGL.parab K (GlobalTheory.SmGL.stdBlocks d h)) ↔
        ∀ j, ∀ y ∈ Y j, (x : Matrix (Fin n) (Fin n) K) *ᵥ y ∈ Y j) ∧
    (∀ x : GL (Fin n) K, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy g (GlobalTheory.SmGL.unipRad K (GlobalTheory.SmGL.stdBlocks d h)) ↔
        ∀ j : Fin m, ∀ y ∈ Y j.succ, (x : Matrix (Fin n) (Fin n) K) *ᵥ y - y ∈ Y j.castSucc) := by
  intro K _ n m Y d h g hY
  set b := GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d h) with hb
  have hGi : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGm : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hz : ∀ x : GL (Fin n) K, (((g⁻¹ * x * g : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) *
        (g : Matrix (Fin n) (Fin n) K) := fun x => by simp only [Units.val_mul]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_conjBy, GlobalTheory.SmGL.mem_parab, hz, ← stab_iff]
    refine forall_congr' fun j => ?_
    have := transport (g : Matrix (Fin n) (Fin n) K) ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      (x : Matrix (Fin n) (Fin n) K) hGi hGm (lowVec b j) (fun _ v => lowVec b j v)
    rw [← this]
    refine forall_congr' fun y => ?_
    rw [hY j y, hY j]
    rfl
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_conjBy, GlobalTheory.RadRev.mem_unipRad_entries, hz, ← rad_iff]
    refine forall_congr' fun j => ?_
    have := transport (g : Matrix (Fin n) (Fin n) K) ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      (x : Matrix (Fin n) (Fin n) K) hGi hGm (lowVec b (j.succ : ℕ)) (fun w v => lowVec b (j.castSucc : ℕ) (v - w))
    rw [← this]
    refine forall_congr' fun y => ?_
    rw [hY j.succ y, hY j.castSucc, mulVec_sub]
    rfl

end GlobalTheory.StdChainStab
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedStandardChainStabilizerRadicalStatement

section

@[expose] public section

open scoped Matrix

theorem _root_.GlobalTheory.T.translated_standard_chain_stabilizer_radical : ∀ {K : Type} [Field K] {n m : ℕ} (Y : Fin (m + 1) → Submodule K (Fin n → K)) (d : Fin m → ℕ) (h : ∑ j, d j = n)
    (g : GL (Fin n) K), (∀ (j : Fin (m + 1)) (y : Fin n → K),
      y ∈ Y j ↔ ∀ i : Fin n, (j : ℕ) ≤ ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d h) i : Fin m) : ℕ) →
        (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) i = 0) →
    (∀ x : GL (Fin n) K, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy g (GlobalTheory.SmGL.parab K (GlobalTheory.SmGL.stdBlocks d h)) ↔
        ∀ j, ∀ y ∈ Y j, (x : Matrix (Fin n) (Fin n) K) *ᵥ y ∈ Y j) ∧
    (∀ x : GL (Fin n) K, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy g (GlobalTheory.SmGL.unipRad K (GlobalTheory.SmGL.stdBlocks d h)) ↔
        ∀ j : Fin m, ∀ y ∈ Y j.succ, (x : Matrix (Fin n) (Fin n) K) *ᵥ y - y ∈ Y j.castSucc) := by
  first | exact @GlobalTheory.StdChainStab.stdChain_stab_rad | exact GlobalTheory.StdChainStab.stdChain_stab_rad | (intros; apply GlobalTheory.StdChainStab.stdChain_stab_rad <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsParabolicIsotropicFlagStabilizerSplitPlace

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.SplitFlag.isParabRad_parAt : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) (𝔉 : IsoFlag V), GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.IsParabRad (parAt 𝔉 s)
      ((NLoc 𝔉 v).map (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))) := by
  intro D V v s 𝔉
  obtain ⟨d, hd, g₀, hg₀⟩ := GlobalTheory.T.exists_gl_adaptedBasis_monotoneSubspaceChain (GlobalTheory.SplitFlag.flagChain 𝔉 s.emb) (GlobalTheory.SplitFlag.flagChain_mono _ _)
    (GlobalTheory.SplitFlag.flagChain_zero _ _) (GlobalTheory.SplitFlag.flagChain_last _ _ s.cm)
  obtain ⟨hP, hN⟩ := GlobalTheory.T.translated_standard_chain_stabilizer_radical _ d hd g₀ hg₀
  have key : ∀ x : GL (Fin V.rank) (Fv D.host.F v),
      splitHom D.sp.cm.sig V.gram s.emb (s.equiv.symm x) = s.basis * x * s.basis⁻¹ := fun x =>
    splitHom_splitEquivIn_symm s.cm s.herm s.emb s.basis x
  have hmap : ∀ (H : Subgroup (GLoc D.sp.cm.sig V.gram v)) (x : GL (Fin V.rank) (Fv D.host.F v)),
      x ∈ H.map (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v)) ↔ s.equiv.symm x ∈ H :=
    fun H x => ⟨by rintro ⟨g, hg, rfl⟩; simpa using hg, fun hx => ⟨_, hx, s.equiv.apply_symm_apply x⟩⟩
  have hconj : ∀ (H : Subgroup (GL (Fin V.rank) (Fv D.host.F v))) (x : GL (Fin V.rank) (Fv D.host.F v)),
      x ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy (s.basis⁻¹ * g₀) H ↔ s.basis * x * s.basis⁻¹ ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy g₀ H := by
    intro H x
    rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_conjBy, GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_conjBy]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  refine ⟨2 * 𝔉.k + 1, d, hd, s.basis⁻¹ * g₀, ?_, ?_⟩
  · ext x
    rw [parAt, hmap, GlobalTheory.T.mem_isotropicFlagParabolic_iff_splitPlaceChain D.sp.cm s.cm s.herm s.emb 𝔉, key, hconj, hP]
  · ext x
    rw [hmap, GlobalTheory.T.mem_isotropic_flag_unipotent_iff_split_chain_trivial D.sp.cm s.cm s.herm s.emb 𝔉, key, hconj, hN]
end
end
end
