module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallInvariantDifferentialDvdStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalGroupLawLogWithLinearPartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSquareCoordinatesPresentLevelsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupFormalLawCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupHomCoordinatesExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionsEqSeriesInChartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfNatMultipleFormalGroupLawStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFormalGroupCocycleIffMemCocyclesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivCocycleMemRangeCobOfPullbackMulPStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalChartQuotientByIdealWithPrimePowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMapNatMultipleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCoboundarySwapPullbackCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesLiftQuotient
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCoboundaryRepresentativeCocycleRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCoboundarySwapPullbackCommuteStatement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfPullbackNmulCoboundary

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup



theorem GlobalTheory.Katz.exists_coboundary_of_pullback_nmul_coboundary' : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ (κ : MvPowerSeries (Fin d ⊕ Fin d) k) (B : MvPowerSeries (Fin d) k), IsCoc μ κ → cob1 μ B = pull2 (nmul μ p) κ → c.ev 1 B = 0 → ∃ s, κ = cob1 μ s := by
  intro p _ k _ d G c μ hμ κ B hκ hB h1
  have hcoc : ∀ s, IsCoc μ s ↔ (fun n => c.ev₂ n s) ∈ G.cocycles := GlobalTheory.T.isSymmetricFormalGroupCocycle_iff_mem_cocycles p k d G c μ hμ
  have hlaw := (GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ
  have hfun := GlobalTheory.T.functions_eq_series_in_chart p k d G c
  have hsq := (GlobalTheory.T.chart_square_coordinates_present_levels p k d G c).2
  have hmap := ((GlobalTheory.T.connectedPDivGroupHom_coordinates_existsUnique p k d d G G c c ((p : ℤ_[p]) • 𝟙 G)).2 (nmul μ p)
    (GlobalTheory.T.isMapOf_natMultiple_formalGroupLaw p k d G c μ hμ p)).2
  let cz : G.cocycles := ⟨fun n => c.ev₂ n κ, (hcoc κ).1 hκ⟩
  let bB : G.funs := ⟨fun n => c.ev n B, fun n => hfun.1 n B⟩
  have key : G.cob bB = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) cz := by
    apply Subtype.ext; funext n
    change cobOne k _ (c.ev n B) = pullbackTwo (((p : ℤ_[p]) • 𝟙 G).app n) (c.ev₂ n κ)
    rw [← (hlaw.2 n B).2, hB, (hmap n).2 κ]
  obtain ⟨b', hb'⟩ := GlobalTheory.T.pDivCocycle_mem_range_cob_of_pullback_mulP G cz bB key h1
  obtain ⟨s, hs, -⟩ := hfun.2.2 b'.1 b'.2
  refine ⟨s, ?_⟩
  obtain ⟨t, -, ht⟩ := hsq (fun n => c.ev₂ n κ) (fun n => hfun.2.1 n κ)
  have e1 := ht κ (fun n => rfl)
  have e2 := ht (cob1 μ s) (fun n => by
    rw [(hlaw.2 n s).2, hs n]
    exact congrArg (fun x : G.cocycles => x.1 n) hb')
  exact e1.trans e2.symm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfPullbackNmulCoboundaryStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_coboundary_of_pullback_nmul_coboundary : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ (κ : MvPowerSeries (Fin d ⊕ Fin d) k) (B : MvPowerSeries (Fin d) k), IsCoc μ κ → cob1 μ B = pull2 (nmul μ p) κ → c.ev 1 B = 0 → ∃ s, κ = cob1 μ s := by
  first | exact @GlobalTheory.Katz.exists_coboundary_of_pullback_nmul_coboundary' | exact GlobalTheory.Katz.exists_coboundary_of_pullback_nmul_coboundary' | (intros; apply GlobalTheory.Katz.exists_coboundary_of_pullback_nmul_coboundary' <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupCocycleCoboundaryModPrime

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.CobModP

theorem constantCoeff_subst_of_zero' {σ τ R : Type} [CommRing R] [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha0 : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have h := constantCoeff_subst_eq_zero ha ha0 (f := f - C (constantCoeff f)) (by simp)
  rw [subst_sub ha, subst_C, map_sub, constantCoeff_C, sub_eq_zero] at h
  exact h

theorem constantCoeff_formalGroupLawCoboundaryOne_eq_zero {R : Type} [CommRing R] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (h : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) R) : constantCoeff (cob1 μ f) = -constantCoeff f := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, constantCoeff_subst_of_zero' h,
    constantCoeff_subst_of_zero' (fun _ => constantCoeff_X _),
    constantCoeff_subst_of_zero' (fun _ => constantCoeff_X _)]
  ring

theorem coboundary_mod_p : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (κ : MvPowerSeries (Fin d ⊕ Fin d) O) (B : MvPowerSeries (Fin d) O) (y : G.A 1), constantCoeff κ = 0 → IsCoc c.μ κ → (∀ α, (p : O) ∣ coeff α (cob1 c.μ B - pull2 (nmul c.μ p) κ)) → c.ev 1 B = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ ∀ α, (p : O) ∣ coeff α (κ - cob1 c.μ t) := by
  intro p _ O _ G d c κ B y hκ0 hcoc hdiv hB
  set I : Ideal O := Ideal.span {(p : O)} with hI
  set r : O →+* O ⧸ I := Ideal.Quotient.mk I with hr
  obtain ⟨c', hlaw, hev, -⟩ := GlobalTheory.T.exists_formalChart_quotient_by_ideal_with_primePow p O G d c I 1 (by
    rw [pow_one]; exact Ideal.mem_span_singleton_self _)
  have hconst := c.isLaw.const
  obtain ⟨hm1, hm2, hm3, -, hm5⟩ := GlobalTheory.T.map_coboundary_swap_pullback_commute O d c.μ hconst (O ⧸ I) r
  obtain ⟨-, hn⟩ := GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple O d c.μ c.isLaw (O ⧸ I) r
  have hnc : ∀ i, constantCoeff (nmul c.μ p i) = 0 := fun i => (hn p i).1
  have hcoc' : IsCoc (fun i => map r (c.μ i)) (map r κ) :=
    ⟨by rw [← hm2, hcoc.1, map_zero], by rw [← hm3, hcoc.2]⟩
  have heq : cob1 (fun i => map r (c.μ i)) (map r B) =
      pull2 (nmul (fun i => map r (c.μ i)) p) (map r κ) := by
    have h0 : map r (cob1 c.μ B - pull2 (nmul c.μ p) κ) = 0 :=
      ((GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I).2.1 _).2
        (fun α => Ideal.mem_span_singleton.2 (hdiv α))
    rw [map_sub, hm1, (hm5 _ hnc).1, sub_eq_zero] at h0
    rw [h0]
    congr 1
    funext i
    exact (hn p i).2
  have hp1 : (p : O) • (1 : O ⧸ I) = 0 := by
    rw [Algebra.smul_def, mul_one]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hev0 : c'.ev 1 (map r B) = 0 := by
    rw [hev, hB, toBase_app, ← TensorProduct.smul_tmul, hp1, TensorProduct.zero_tmul]
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_coboundary_of_pullback_nmul_coboundary p (O ⧸ I) d (G.baseChange (O ⧸ I)) c' _ hlaw (map r κ) (map r B)
    hcoc' heq hev0
  have hs0 : constantCoeff s = 0 := by
    have h1 : constantCoeff (map r κ) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hκ0,
        map_zero]
    have hc' : ∀ i, constantCoeff (map r (c.μ i)) = 0 := fun i => by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        hconst i, map_zero]
    rw [hs, constantCoeff_formalGroupLawCoboundaryOne_eq_zero hc'] at h1
    exact neg_eq_zero.1 h1
  obtain ⟨t, ht, ht0⟩ := (GlobalTheory.mvPowerSeries_lift_quotient O (Fin d) I).1 s
  refine ⟨t, ht0 hs0, fun α => ?_⟩
  have h2 : map r (κ - cob1 c.μ t) = 0 := by rw [map_sub, hm1, ht, hs, sub_self]
  exact Ideal.mem_span_singleton.1 (((GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I).2.1 _).1 h2 α)

end GlobalTheory.CobModP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupCocycleCoboundaryModPrimeStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.formalGroupCocycle_coboundary_mod_prime : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (κ : MvPowerSeries (Fin d ⊕ Fin d) O) (B : MvPowerSeries (Fin d) O) (y : G.A 1), constantCoeff κ = 0 → IsCoc c.μ κ → (∀ α, (p : O) ∣ coeff α (cob1 c.μ B - pull2 (nmul c.μ p) κ)) → c.ev 1 B = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ ∀ α, (p : O) ∣ coeff α (κ - cob1 c.μ t) := by
  first | exact @GlobalTheory.CobModP.coboundary_mod_p | exact GlobalTheory.CobModP.coboundary_mod_p | (intros; apply GlobalTheory.CobModP.coboundary_mod_p <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralCoboundaryDivisibleOfQuasiLogDefec

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem exists_int_cob_dvd_of_defect_ev :
    ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E) (s : MvPowerSeries (Fin d) O) (y : G.A 1), QL c.μ ⊤ f → map (algebraMap O E) s = defect c.μ p f → c.ev 1 s = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ In (Ideal.span {(p : O)}) (cob1 (up E c.μ) (f - map (algebraMap O E) t)) := by
  intro p _ O E _ _ _ hF G d c f s y hQL hs hy
  obtain ⟨hf0, -, hcob⟩ := hQL
  choose bκ _ hbκ using hcob
  set κ : MvPowerSeries (Fin d ⊕ Fin d) O := fun α => bκ α with hκdef
  have hκ : map (algebraMap O E) κ = cob1 (up E c.μ) f := by
    ext α
    rw [coeff_map, hbκ α]
    rfl
  obtain ⟨hcoc, hκ0, hdef⟩ := GlobalTheory.T.integral_coboundary_representative_cocycle_rules O E d c.μ c.isLaw hF.inj f κ hκ
  have hrel := (hdef p s hs).1
  have hμ0 := c.isLaw.const
  have hneg : cob1 c.μ (-s) = -cob1 c.μ s := by
    rw [← neg_one_smul O s, formalCoboundary_smul hμ0, neg_one_smul]
  obtain ⟨t, ht0, htd⟩ := GlobalTheory.T.formalGroupCocycle_coboundary_mod_prime p O G d c κ (-s) (-y) (hκ0 hf0) hcoc
    (fun α => by
      rw [hneg, hrel, show -((p : O) • κ - pull2 (nmul c.μ p) κ) - pull2 (nmul c.μ p) κ
        = -((p : O) • κ) by ring, map_neg, coeff_smul]
      exact (Dvd.intro _ rfl).neg_right)
    (by rw [map_neg, hy, smul_neg])
  refine ⟨t, ht0, fun α => ⟨coeff α (κ - cob1 c.μ t), Ideal.mem_span_singleton.2 (htd α), ?_⟩⟩
  have hup0 : ∀ i, constantCoeff (up E c.μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ0, map_zero]
  have hadd := formalCoboundary_add hup0 (f - map (algebraMap O E) t) (map (algebraMap O E) t)
  rw [sub_add_cancel] at hadd
  have hmap := (GlobalTheory.T.map_coboundary_swap_pullback_commute O d c.μ hμ0 E (algebraMap O E)).1 t
  have hsub : cob1 (up E c.μ) (f - map (algebraMap O E) t) =
      map (algebraMap O E) (κ - cob1 c.μ t) := by
    rw [map_sub, hmap, hκ]
    exact eq_sub_of_add_eq hadd.symm
  rw [hsub, coeff_map]

end GlobalTheory.QLog
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralCoboundaryDivisibleOfQuasiLogDefecStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_integral_coboundary_divisible_of_quasiLog_defect : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E) (s : MvPowerSeries (Fin d) O) (y : G.A 1), QL c.μ ⊤ f → map (algebraMap O E) s = defect c.μ p f → c.ev 1 s = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ In (Ideal.span {(p : O)}) (cob1 (up E c.μ) (f - map (algebraMap O E) t)) := by
  first | exact @GlobalTheory.QLog.exists_int_cob_dvd_of_defect_ev | exact GlobalTheory.QLog.exists_int_cob_dvd_of_defect_ev | (intros; apply GlobalTheory.QLog.exists_int_cob_dvd_of_defect_ev <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntLogOfIsLiePSmul

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem GlobalTheory.QLog.exists_int_log_of_isLie_p_smul : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), QL c.μ ⊤ f → c.IsLie f ((p : O) • l) → ∃ (s : MvPowerSeries (Fin d) O) (g : MvPowerSeries (Fin d) E), cob1 (up E c.μ) g = 0 ∧ QL c.μ (Ideal.span {(p : O)}) (f - map (algebraMap O E) s - g) := by
  intro p _ O E _ _ _ hF G d c f l hf hl
  obtain ⟨s₁, hs₁, hl₁⟩ := (c.isLie_iff hF.inj f _).1 hl 1
  rw [pow_one] at hs₁
  have hdiv : ∀ (w : G.dual.omega) (φ : CartierDual O (G.A 1)), dUnit (R := O) φ = w.1 1 →
      (p : O) ∣ φ (c.ev 1 s₁) := by
    intro w φ hφ
    have h1 := hl₁ w φ hφ
    rw [pow_one, LinearMap.smul_apply, smul_eq_mul] at h1
    exact (dvd_sub_right (dvd_mul_right _ _)).1 h1
  obtain ⟨⟨z, hz⟩, -⟩ := GlobalTheory.T.dvd_of_forall_invariantDifferential_dvd p O G 1 (p : O) (c.ev 1 s₁) hdiv
  obtain ⟨t, ht0, ht⟩ := GlobalTheory.T.exists_integral_coboundary_divisible_of_quasiLog_defect p O E hF G d c f s₁ z hf hs₁ hz
  obtain ⟨hf0, hflin, -⟩ := hf
  choose b _ hb using hflin
  obtain ⟨g, hg0, hglin, hgcob⟩ := GlobalTheory.T.exists_formalGroupLaw_log_with_linearPart p O E hF d c.μ c.isLaw (fun i => b i - lin t i)
  have hμ : ∀ i, constantCoeff (up E c.μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      c.isLaw.const i, map_zero]
  refine ⟨t, g, hgcob, ?_, ?_, ?_⟩
  · rw [map_sub, map_sub, hf0, hg0, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
      coeff_zero_eq_constantCoeff_apply, ht0, map_zero]
    simp
  · intro i
    refine ⟨0, Ideal.zero_mem _, ?_⟩
    have : lin (f - map (algebraMap O E) t - g) i = lin f i - algebraMap O E (lin t i) - lin g i := by
      simp [lin, coeff_map]
    rw [this, hb i, hglin i, map_sub, map_zero]
    simp
  · have hsub : f - map (algebraMap O E) t - g = (f - map (algebraMap O E) t) + (-1 : E) • g := by
      rw [neg_one_smul, ← sub_eq_add_neg]
    rw [hsub, formalCoboundary_add hμ, formalCoboundary_smul hμ, hgcob, smul_zero, add_zero]
    exact ht
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDecompositionOfTangentDivisibleByP

section

@[expose] public section

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLogInj

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), QL c.μ ⊤ f → c.IsLie f ((p : O) • l) → ∃ (s : MvPowerSeries (Fin d) O) (g : MvPowerSeries (Fin d) E), cob1 (up E c.μ) g = 0 ∧ QL c.μ (Ideal.span {(p : O)}) (f - map (algebraMap O E) s - g) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c E _ _ hE f l hf hL
  exact GlobalTheory.QLog.exists_int_log_of_isLie_p_smul p O E hE G d c f l hf hL

end GlobalTheory.QLogInj
end
end
