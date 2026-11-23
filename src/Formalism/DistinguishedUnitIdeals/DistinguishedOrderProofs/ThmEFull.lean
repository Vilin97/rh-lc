module

public import Formalism.DistinguishedUnitIdeals.WordConsts
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.ArcLiftOfLocalizationData
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.DescentEstimateDownUp
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.GroundTheory
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.LevelsModConstIffOfDownDown
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.LevelsModConstIffOfNoDown
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.LinExtEqZeroOfMemExt
public import Formalism.DistinguishedUnitIdeals.StatementE
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
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.RhoMapFunctorial
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.SplittingOfPositiveLevel
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.BaseGamC

section

@[expose] public section

noncomputable section

namespace Formalism.ExponentWindows.E

open PowerSeries

namespace PhiGammaCoboundaries

section
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V]

theorem base_phi_C (B : Base O) (m : O) : B.φ (C m) = C m := by
  rw [← PowerSeries.algebraMap_eq]
  exact B.φ.commutes m

theorem base_gam_C (B : Base O) (m : O) : B.γ (C m) = C m := by
  rw [← PowerSeries.algebraMap_eq]
  exact B.γ.commutes m

theorem cob_zero (L : Lat B n V) : L.IsCobound 0 0 := by
  exact ⟨0, by funext i; simp [Lat.dφ], by funext i; simp [Lat.dγ]⟩

theorem cob_add (L : Lat B n V) {y z y' z' : ZMod n → V} (h : L.IsCobound y z)
    (h' : L.IsCobound y' z') : L.IsCobound (y + y') (z + z') := by
  obtain ⟨m, rfl, rfl⟩ := h
  obtain ⟨m', rfl, rfl⟩ := h'
  refine ⟨m + m', ?_, ?_⟩ <;> funext i <;> simp only [Lat.dφ, Lat.dγ, Pi.add_apply, map_add (f := _)] <;> abel

theorem cob_neg (L : Lat B n V) {y z : ZMod n → V} (h : L.IsCobound y z) :
    L.IsCobound (-y) (-z) := by
  obtain ⟨m, rfl, rfl⟩ := h
  refine ⟨-m, ?_, ?_⟩ <;> funext i <;> simp only [Lat.dφ, Lat.dγ, Pi.neg_apply, map_neg] <;> abel

theorem cob_sub (L : Lat B n V) {y z y' z' : ZMod n → V} (h : L.IsCobound y z)
    (h' : L.IsCobound y' z') : L.IsCobound (y - y') (z - z') := by
  simpa [sub_eq_add_neg] using cob_add L h (cob_neg L h')

theorem cob_smul (L : Lat B n V) (a : O) {y z : ZMod n → V} (h : L.IsCobound y z) :
    L.IsCobound (C a • y) (C a • z) := by
  obtain ⟨m, rfl, rfl⟩ := h
  refine ⟨C a • m, ?_, ?_⟩ <;> funext i <;>
    simp only [Lat.dφ, Lat.dγ, Pi.smul_apply, L.φ_semi, L.γ_semi, base_phi_C, base_gam_C, smul_sub]

theorem cob_sum (L : Lat B n V) {ι : Type} (s : Finset ι) (y z : ι → ZMod n → V)
    (h : ∀ c ∈ s, L.IsCobound (y c) (z c)) :
    L.IsCobound (∑ c ∈ s, y c) (∑ c ∈ s, z c) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simpa using cob_zero L) ?_
  intro c s hc ih h
  rw [Finset.sum_insert hc, Finset.sum_insert hc]
  exact cob_add L (h c (Finset.mem_insert_self c s))
    (ih fun c' hc' => h c' (Finset.mem_insert_of_mem hc'))

theorem lc_pow (B : Base O) (k : ℕ) : B.lc ^ k = C ((B.ℓ : O) ^ k) := by
  unfold Base.lc
  rw [map_pow]

end

theorem combine {O : Type} [CommRing O] {n : ℕ} {V₁ V₂ : Type} [AddCommGroup V₁]
    [Module (PowerSeries O) V₁] [AddCommGroup V₂] [Module (PowerSeries O) V₂]
    (f : V₁ →ₗ[PowerSeries O] V₂) (s : Finset (ZMod n)) (l : O) (e e₁ e₂ : ℕ) (he : e = e₂ + e₁)
    (a m : ZMod n → O) (ham : ∀ c ∈ s, a c * m c = l ^ e₂)
    (y₀ : ZMod n → V₂) (yc : ZMod n → ZMod n → V₂) (y1 : ZMod n → ZMod n → V₁) :
    (C (l ^ e) • y₀ - fun i => f ((∑ c ∈ s, C (a c) • y1 c) i)) =
      C (l ^ e₂) • (C (l ^ e₁) • y₀ - ∑ c ∈ s, yc c) -
        ∑ c ∈ s, C (a c) • ((fun i => f (y1 c i)) - C (m c) • yc c) := by
  subst he
  funext i

  simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, map_sum, map_smul, smul_sub,
  Finset.smul_sum, Finset.sum_sub_distrib, smul_smul]
  have h1 : ∑ c ∈ s, (C (a c) * C (m c)) • yc c i = ∑ c ∈ s, C (l ^ e₂) • yc c i :=
    Finset.sum_congr rfl fun c hc => by rw [← map_mul, ham c hc]
  rw [h1, pow_add, map_mul]
  abel

end PhiGammaCoboundaries

open PhiGammaCoboundaries in
theorem thmE_of (h1 : RhoExists) (h2 : RhoLin) (h3 : RhoFun) (h4 : Step1) : ThmEAssembly := by
  intro O _ B n _ Cu abelian₂ j M g sig rr a₀ kap V₁ V₂ V₀ _ _ _ _ _ _ L₁ L₂ L₀ e₀ h Zf₁ Zf₂
    hM hB hG1 hG2 hell he1 he2 hZsmul hZrho hZext hW κ hκ
  obtain ⟨Y, hYrep, hYgood⟩ := hZext κ hκ
  obtain ⟨w, yc, zc, hwc, hcob⟩ := h4 O B n Cu abelian₂ j M g sig rr V₂ V₀ L₂ L₀ e₀ Y κ.1 κ.2 hM hB
    hG2 hell he1 he2 hYrep hYgood
  have H : ∀ c ∈ Cu.cuts, ∃ (w' : V₁) (k : ℕ) (ε : Oˣ), k ≤ 2 * kap ∧ L₁.Wc Cu abelian₂ c w' ∧
      h.f w' - C ((ε : O) * (B.ℓ : O) ^ (2 * sig + 2 * a₀ + rr + k)) • w c ∈ sm X (L₂.N c) :=
    fun c hc => hW c hc (w c) (hwc c hc).1
  choose! W1 K E hK hW1 hD using H
  have H2 : ∀ c ∈ Cu.cuts, ∃ y z : ZMod n → V₁, L₁.IsRho c j M g sig (W1 c) y z :=
    fun c hc => h1 O B n Cu j M g sig V₁ L₁ hB hG1 c hc (W1 c) (hW1 c hc).1
  choose! Y1 Z1 hR using H2
  let mc : ZMod n → O := fun c => (E c : O) * (B.ℓ : O) ^ (2 * sig + 2 * a₀ + rr + K c)
  let ac : ZMod n → O := fun c => (((E c)⁻¹ : Oˣ) : O) * (B.ℓ : O) ^ (2 * kap - K c)
  have ham : ∀ c ∈ Cu.cuts, ac c * mc c = (B.ℓ : O) ^ (rr + 2 * sig + 2 * a₀ + 2 * kap) := by
    intro c hc
    have hk := hK c hc
    calc ac c * mc c = ((((E c)⁻¹ : Oˣ) : O) * (E c : O)) *
          ((B.ℓ : O) ^ (2 * kap - K c) * (B.ℓ : O) ^ (2 * sig + 2 * a₀ + rr + K c)) := by
          simp only [ac, mc]; ring
      _ = _ := by
          rw [Units.inv_mul, one_mul, ← pow_add]
          congr 1
          omega
  have hlin : ∀ c ∈ Cu.cuts, L₂.IsCobound ((fun i => h.f (Y1 c i)) - C (mc c) • yc c)
      ((fun i => h.f (Z1 c i)) - C (mc c) • zc c) := fun c hc =>
    h2 O B n Cu j M g sig V₂ L₂ hB hG2 c hc (mc c) (w c) (h.f (W1 c)) (yc c) (zc c) _ _
      (hwc c hc).2 (h3 O B n j M g sig V₁ V₂ L₁ L₂ h c (W1 c) (Y1 c) (Z1 c) (hR c hc)) (hD c hc)
  refine ⟨∑ c ∈ Cu.cuts, (C (ac c) • Y1 c, C (ac c) • Z1 c), ?_, ?_⟩
  · exact AddSubgroup.sum_mem _ fun c hc =>
      hZsmul (ac c) (Y1 c, Z1 c) (hZrho c hc (W1 c) (hW1 c hc) (Y1 c) (Z1 c) (hR c hc))
  · have e : 2 * rr + 4 * sig + 2 * a₀ + 2 * kap =
        (rr + 2 * sig + 2 * a₀ + 2 * kap) + (rr + 2 * sig) := by ring
    simp only [lc_pow] at hcob ⊢
    simp only [Prod.fst_sum, Prod.snd_sum]
    rw [e, combine h.f Cu.cuts (B.ℓ : O) _ (rr + 2 * sig) (rr + 2 * sig + 2 * a₀ + 2 * kap) rfl
        ac mc ham κ.1 yc Y1,
      combine h.f Cu.cuts (B.ℓ : O) _ (rr + 2 * sig) (rr + 2 * sig + 2 * a₀ + 2 * kap) rfl
        ac mc ham κ.2 zc Z1]
    exact cob_sub L₂ (cob_smul L₂ _ hcob)
      (cob_sum L₂ Cu.cuts _ _ fun c hc => cob_smul L₂ (ac c) (hlin c hc))

end Formalism.ExponentWindows.E
end
end
end

-- Source module: Formalism.DistinguishedUnitIdeals.FinalE

section

@[expose] public section

namespace Formalism.ExponentWindows.E

theorem theorem_E_assembled : ThmEAssembly :=
  thmE_of rho_map_exists rho_map_linear rho_map_functorial splitting_of_extension

end Formalism.ExponentWindows.E
end
end

-- Source module: Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.ThmEFull

section

@[expose] public section

namespace Formalism.ExponentWindows.E.Full

open PowerSeries

theorem constLift_of_word {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {ℓ ell r₁ r₂ a₀ rr : ℕ} {p : ℕ → PowerSeries O} {H b : ℕ → ℕ}
    {kind : ℕ → Kind} {U₁ : ℕ → Submodule O (Fin r₁ → O)} {U₂ : ℕ → Submodule O (Fin r₂ → O)}
    {prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)}
    (hS : LevelModelSetting ϖ ℓ ell p H b kind U₁ U₂) (hL : LLift ℓ rr prL) (hr : rr ≤ 2 * a₀)
    (hW : ArcWord ϖ ℓ ell a₀ p b kind U₁ U₂ prL) :
    ConstLift ϖ ℓ p H b kind U₁ U₂ ell a₀ prL := by
  obtain ⟨cN, cD, cDU, cDD, cUD⟩ := CL.lifts_mod_const_of_words
  rcases hW with hW | hW | hW | hW | hW
  · exact cN levels_mod_const_iff_of_no_down O ϖ hϖ ℓ ell r₁ r₂ a₀ p H b kind U₁ U₂ prL hS hW
  · obtain ⟨s₁, h1, h2, h3⟩ := hW
    exact cD descent_estimate_down O ϖ hϖ ℓ ell r₁ r₂ a₀ rr p H b kind U₁ U₂ prL hS hL hr s₁ h1 h2 h3
  · obtain ⟨s₀, s₁, h0, h1, h2, h3, h4, h5⟩ := hW
    exact cDU descent_estimate_down_up O ϖ hϖ ℓ ell r₁ r₂ a₀ rr p H b kind U₁ U₂ prL hS hL hr s₀ s₁ h0 h1 h2 h3
      h4 h5
  · obtain ⟨s₀, s₁, h0, h1, h2, h3, h4, ρ, fρ, h5, h6, h7, h8⟩ := hW
    exact cDD levels_mod_const_iff_of_down_down O ϖ hϖ ℓ ell r₁ r₂ a₀ rr p H b kind U₁ U₂ prL hS hL hr s₀ s₁ h0 h1 h2 h3
      h4 ρ fρ h5 h6 h7 h8
  · obtain ⟨s₀, s₁, h0, h1, h2, h3, h4, hC, c, α, β, h5, h6⟩ := hW
    exact cUD descent_estimate_up_down O ϖ hϖ ℓ ell r₁ r₂ a₀ rr p H b kind U₁ U₂ prL hS hL hr s₀ s₁ h0 h1 h2 h3
      h4 hC c α β h5 h6

section
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem pow_mem_pair {ϖ : O} {p₁ p₀ : PowerSeries O} (h : CoprimeRat ϖ p₁ p₀) (b₁ b₀ : ℕ) :
    ∃ N : ℕ, C (ϖ ^ N) ∈ Ideal.span {p₁ ^ b₁, p₀ ^ b₀} := by
  unfold CoprimeRat at h
  obtain ⟨N, a, a', hN⟩ := h
  refine ⟨N * (b₁ + b₀), ?_⟩
  have hmem : C (ϖ ^ N) ∈ Ideal.span {p₁} ⊔ Ideal.span {p₀} := by
    rw [← hN]
    exact add_mem (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
  have h2 : C (ϖ ^ N) ^ (b₁ + b₀) ∈ (Ideal.span {p₁} ⊔ Ideal.span {p₀}) ^ (b₁ + b₀) :=
    Ideal.pow_mem_pow hmem _
  have h3 := Ideal.sup_pow_add_le_pow_sup_pow h2
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h3
  rw [pow_mul, map_pow, Ideal.span_insert]
  exact h3

theorem consts_DD {ϖ : O} {p₁ p₀ : PowerSeries O} (h : CoprimeRat ϖ p₁ p₀) (b₁ b₀ : ℕ) :
    ∃ (ρ : ℕ) (fρ : PowerSeries O),
      C (ϖ ^ ρ) ∈ Ideal.span {p₁ ^ b₁, p₀ ^ b₀} ∧
      (∀ k : ℕ, C (ϖ ^ k) ∈ Ideal.span {p₁ ^ b₁, p₀ ^ b₀} → ρ ≤ k) ∧
      fρ ∈ Ideal.span {p₁ ^ b₁} ∧ fρ - C (ϖ ^ ρ) ∈ Ideal.span {p₀ ^ b₀} := by
  classical
  have hex := pow_mem_pair h b₁ b₀
  have hρ : C (ϖ ^ Nat.find hex) ∈ Ideal.span {p₁ ^ b₁, p₀ ^ b₀} := Nat.find_spec hex
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp hρ
  refine ⟨Nat.find hex, x * p₁ ^ b₁, hρ, fun k hk => Nat.find_min' hex hk,
    Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), ?_⟩
  rw [← hxy]
  have e : x * p₁ ^ b₁ - (x * p₁ ^ b₁ + y * p₀ ^ b₀) = (-y) * p₀ ^ b₀ := by ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem consts_UD {ϖ : O} (hϖ : Irreducible ϖ) {d : ℕ} (hd : 1 ≤ d) {p₁ p₀ : PowerSeries O}
    (hp₀ : UnitDist ϖ d p₀) (h : CoprimeRat ϖ p₁ p₀) (b₁ b₀ : ℕ) (hb : 1 ≤ b₀) :
    ∃ (c : ℕ) (α β : PowerSeries O),
      p₁ ^ b₁ = C (ϖ ^ c) * α + p₀ ^ b₀ * β ∧
      p₁ ^ b₁ ∉ Ideal.span {C (ϖ ^ (c + 1)), p₀ ^ b₀} := by
  classical
  obtain ⟨N, hN⟩ := pow_mem_pair h b₁ b₀
  have hex : ∃ c : ℕ, p₁ ^ b₁ ∉ Ideal.span {C (ϖ ^ (c + 1)), p₀ ^ b₀} := by
    refine ⟨N, fun hmem => ?_⟩
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hmem
    obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 hN
    have h1 : C (ϖ ^ N) * (1 - C ϖ * (x * u)) ∈ Ideal.span {p₀ ^ b₀} := by
      rw [Ideal.mem_span_singleton]
      refine ⟨x * v + y, ?_⟩
      have e : C (ϖ ^ (N + 1)) = C (ϖ ^ N) * C ϖ := by rw [pow_succ, map_mul]
      rw [e] at huv
      calc C (ϖ ^ N) * (1 - C ϖ * (x * u))
          = C (ϖ ^ N) - x * (u * (C (ϖ ^ N) * C ϖ)) := by ring
        _ = (x * p₁ ^ b₁ + y * p₀ ^ b₀) - x * (u * (C (ϖ ^ N) * C ϖ)) := by rw [hxy]
        _ = (x * (u * (C (ϖ ^ N) * C ϖ) + v * p₀ ^ b₀) + y * p₀ ^ b₀)
              - x * (u * (C (ϖ ^ N) * C ϖ)) := by rw [huv]
        _ = p₀ ^ b₀ * (x * v + y) := by ring
    have h2 := mem_span_pow_of_uniformizer_mul O ϖ hϖ d p₀ hp₀ b₀ N _ h1
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 h2
    have h3 := congrArg (coeff 0) hw
    have h0 := constantCoeff_mem_of_unitDist ϖ d p₀ hp₀ hd
    obtain ⟨e0, he0⟩ := Ideal.mem_span_singleton.1 h0
    obtain ⟨b', rfl⟩ : ∃ b', b₀ = b' + 1 := ⟨b₀ - 1, by omega⟩
    simp only [coeff_zero_eq_constantCoeff, map_sub, map_one, map_mul, map_pow,
      constantCoeff_C] at h3 he0
    have : ϖ ∣ 1 := by
      refine ⟨constantCoeff x * constantCoeff u +
        e0 * (constantCoeff p₀) ^ b' * constantCoeff w, ?_⟩
      have h4 : (1 : O) = ϖ * (constantCoeff x * constantCoeff u) +
          (constantCoeff p₀) ^ (b' + 1) * constantCoeff w := by rw [← h3]; ring
      have h5 : (constantCoeff p₀) ^ (b' + 1) = (constantCoeff p₀) ^ b' * (ϖ * e0) := by
        rw [← he0, pow_succ]
      rw [h5] at h4
      rw [h4]
      ring
    exact hϖ.not_isUnit (isUnit_of_dvd_one this)
  have hs := Nat.find_spec hex
  have hmem : p₁ ^ b₁ ∈ Ideal.span {C (ϖ ^ (Nat.find hex)), p₀ ^ b₀} := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · rw [h0, pow_zero, map_one]
      have : Ideal.span {(1 : PowerSeries O), p₀ ^ b₀} = ⊤ :=
        Ideal.eq_top_of_unit_mem _ 1 1 (Ideal.subset_span (by simp)) (one_mul 1)
      rw [this]; trivial
    · obtain ⟨c', hc'⟩ : ∃ c', Nat.find hex = c' + 1 := ⟨Nat.find hex - 1, by omega⟩
      have := Nat.find_min hex (m := c') (by omega)
      rw [hc']
      exact not_not.1 this
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hmem
  exact ⟨Nat.find hex, u, v, huv.symm.trans (by ring), hs⟩

end

end Formalism.ExponentWindows.E.Full

namespace Formalism.ExponentWindows.E

open PowerSeries

theorem word_constants_holds : WordConsts := by
  unfold WordConsts
  intro O _ _ _ ϖ hϖ ℓ ell p b hℓ hP s₀ s₁ h01 h1e
  unfold DistinguishedFamily at hP
  have hs₀ : s₀ < ell := lt_trans h01 h1e
  have hc : CoprimeRat ϖ (p s₁) (p s₀) := hP.2 s₁ h1e s₀ hs₀ (ne_of_gt h01)
  refine ⟨Full.consts_DD hc _ _, fun hb => Full.consts_UD hϖ ?_ (hP.1 s₀ hs₀) hc _ _ hb⟩
  exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))

theorem theorem_E_full_form : ThmEFull := by
  intro O _ _ _ ϖ hϖ B n _ Cu abelian₂ j M g sig rr a₀ kap V₁ V₂ V₀ _ _ _ _ _ _ L₁ L₂ L₀ e₀ h Zf₁ Zf₂
    hM hB hL₁ hL₂ h1 h2 h3 h4 h5 h6 hr hA
  refine theorem_E_assembled O B n Cu abelian₂ j M g sig rr a₀ kap V₁ V₂ V₀ L₁ L₂ L₀ e₀ h Zf₁ Zf₂ hM hB
    hL₁ hL₂ h1 h2 h3 h4 h5 h6 ?_
  intro c hc
  obtain ⟨r₁, r₂, S₁, S₂, m, H, b, kind, U₁, U₂, PP, PP', a1, a2, a3, a4, a5, a6, a7, a8, a9,
    a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27⟩ :=
    hA c hc
  exact arc_lift_of_localization_data O B n Cu abelian₂ g sig rr a₀ kap V₁ V₂ L₁ L₂ h c r₁ r₂ S₁ S₂ m ϖ H b kind U₁ U₂
    PP PP' a1 hB.1 (hL₂.1 c) a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20
    a21 a22 a23 (Full.constLift_of_word hϖ a25 a26 hr a27) a24

end Formalism.ExponentWindows.E
end
end
