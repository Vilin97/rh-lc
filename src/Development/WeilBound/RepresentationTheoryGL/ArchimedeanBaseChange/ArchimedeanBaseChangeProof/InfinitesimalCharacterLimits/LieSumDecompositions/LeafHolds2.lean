module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SplitInv
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.CptRepMemTypePart
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.IntegrableDescendSupP
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.GrowPHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundOfNatDegree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeOfBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UpdateLeUpdate
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.AutomorphicLipschitz.NiceAut
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.BoxVolumes.ExistsMeasureLeProd
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConjugationDifferences.ExpDivExpEq
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConstantTermSteps.CtstepglueHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.TopNeg
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UniformInitialGrowth.InitBnd
import GroundTheory.AutomorphicForms.QuotientMeasure
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTw
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTwA
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.ReLtRho

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary PositivityTheory.Rg.Rs
open scoped Pointwise ENNReal

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

namespace Grow

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem leftInv {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g) :
    ∀ γ ∈ latticeGL E N, ∀ g, φ.1 (γ * g) = φ.1 g := by
  let S : Subgroup (GA E N) :=
    { carrier := {γ | ∀ g, φ.1 (γ * g) = φ.1 g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
      inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }
  have : latticeGL E N ≤ S := sup_le (by rintro _ ⟨γ, rfl⟩; exact hφ.left γ) (Subgroup.zpowers_le.2 (hcen 1))
  exact this

theorem exists_kill {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g)
    {r : ℕ} (hr0 : 0 < r) (hrN : r < N) :
    ∃ p : ℂ[X], p.Monic ∧ An.Kill r φ.1 p ∧ ∀ z, p.IsRoot z → ∃ c ∈ Exp r φ.1, z = Complex.exp c := by
  obtain ⟨hA, hS, _, hCT⟩ := dict_holds E N
  have hcen' : ∀ (t : ℝ) g, φ.1 (An.tor E (fun _ => t) * g) = φ.1 g := fun t g => by
    rw [← hS]; exact hcen t g
  have hnice := niceAut_holds E N φ hφ hcen'
  have hct := (hCT φ hφ r hr0 hrN).1
  have hfin := finTr_holds E N φ hφ r hr0 hrN _ hct
  have hadd : ∀ s t, aT E N r (s + t) = aT E N r s * aT E N r t := fun s t => by
    rw [hA, hA, hA]; exact JSqIntGlue.aR_add r s t
  have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E N r t * g) := by
    intro g
    have e : (fun t => An.ctn r φ.1 (aT E N r t * g)) = fun t => An.ctn r φ.1 (An.aR E N r t * g) :=
      funext fun t => by rw [hA]
    rw [e]
    exact JSqIntGlue.continuous_ctn_comp hnice.cont r ((JSqIntGlue.continuous_aR r).mul continuous_const)
  obtain ⟨p, hp, hpk, hroots⟩ := killPoly_holds (GA E N) (aT E N r) (An.ctn r φ.1) hadd hcont hfin
  refine ⟨p, hp, fun g => ?_, fun z hz => ?_⟩
  · have := hpk g
    simpa only [hA] using this
  · obtain ⟨c, rfl, F, hF, hF0, hFe⟩ := hroots z hz
    exact ⟨c, ⟨_, hct, F, hF, hF0, hFe⟩, rfl⟩

theorem bnd_of' {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g)
    (κ : ℕ → ℝ) (hκ : ∀ r, 0 < r → r < N → ∃ p : ℂ[X], p.Monic ∧ An.Kill r φ.1 p ∧
      ∀ z, p.IsRoot z → ‖z‖ < Real.exp (κ r)) : An.Bnd φ.1 κ := by
  obtain ⟨_, hS, _, _⟩ := dict_holds E N
  have hcen' : ∀ (t : ℝ) g, φ.1 (An.tor E (fun _ => t) * g) = φ.1 g := fun t g => by
    rw [← hS]; exact hcen t g
  have hnice := niceAut_holds E N φ hφ hcen'
  obtain ⟨M, hM⟩ := initBnd_holds E N φ hφ hcen'
  exact GlobalTheory.CompanionTheory.AnBoot.bootGlue diffstep_holds (ctstepglue_holds GlobalTheory.CompanionTheory.LinRec.recBound) E N φ.1 M κ hnice hM hκ

theorem bnd_of {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g)
    (κ : ℕ → ℝ) (hκ : ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re < κ r) : An.Bnd φ.1 κ := by
  refine bnd_of' hφ hcen κ fun r hr0 hrN => ?_
  obtain ⟨p, hp, hk, hroots⟩ := exists_kill hφ hcen hr0 hrN
  refine ⟨p, hp, hk, fun z hz => ?_⟩
  obtain ⟨c, hc, rfl⟩ := hroots z hz
  rw [Complex.norm_exp]
  exact Real.exp_lt_exp.2 (hκ r hr0 hrN c hc)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem re_le_rho {r : ℕ} {c : ℂ} (h : pE E N r c ≤ 0) : c.re ≤ An.rho E N r := by
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  unfold pE at h
  have h2 : c.re / (Module.finrank ℚ E : ℝ) ≤ (r : ℝ) * ((N : ℝ) - r) / 2 := by linarith
  have h3 := (div_le_iff₀ hd).1 h2
  unfold An.rho
  calc c.re ≤ (r : ℝ) * ((N : ℝ) - r) / 2 * (Module.finrank ℚ E : ℝ) := h3
    _ = _ := by ring

omit [_root_.NumberField.IsTotallyComplex E] in
theorem re_lt_rho {r : ℕ} {c : ℂ} (h : pE E N r c < 0) : c.re < An.rho E N r := by
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  unfold pE at h
  have h2 : c.re / (Module.finrank ℚ E : ℝ) < (r : ℝ) * ((N : ℝ) - r) / 2 := by linarith
  have h3 := (div_lt_iff₀ hd).1 h2
  unfold An.rho
  calc c.re < (r : ℝ) * ((N : ℝ) - r) / 2 * (Module.finrank ℚ E : ℝ) := h3
    _ = _ := by ring

end Grow

open Grow in
theorem growPHolds : GrowPHolds := by
  intro E _ _ _ N χ hχ hcen hnp
  refine ⟨ContAut.continuous_of_isOpen_stab E N χ hχ.level, leftInv hχ hcen, fun ε hε => ?_⟩
  exact bnd_of hχ hcen _ fun r hr0 hrN c hc => by
    have := re_le_rho (hnp r hr0 hrN c hc)
    linarith

open Grow in
theorem growQHolds : GrowQHolds := by
  intro E _ _ _ N u hu hsq
  have hcen := hsq.1
  have hk : ∀ r, ∃ κ : ℝ, 0 < r → r < N → κ < An.rho E N r ∧ ∃ p : ℂ[X], p.Monic ∧ An.Kill r u.1 p ∧
      ∀ z, p.IsRoot z → ‖z‖ < Real.exp κ := by
    intro r
    by_cases hr : 0 < r ∧ r < N
    swap
    · exact ⟨0, fun h1 h2 => (hr ⟨h1, h2⟩).elim⟩
    obtain ⟨hr0, hrN⟩ := hr
    obtain ⟨p, hp, hpk, hroots⟩ := exists_kill hu hcen hr0 hrN
    have hroot' : ∀ z ∈ p.roots.toFinset, ‖z‖ < Real.exp (An.rho E N r) := by
      intro z hz
      rw [Multiset.mem_toFinset, mem_roots hp.ne_zero] at hz
      obtain ⟨c, hc, rfl⟩ := hroots z hz
      rw [Complex.norm_exp]
      exact Real.exp_lt_exp.2 (re_lt_rho (expNeg_holds E N u hu hsq r hr0 hrN c hc))
    obtain ⟨κ, hκ, hκz⟩ := JSqIntGlue.exists_lt_of_finset _ _ hroot'
    refine ⟨κ, fun _ _ => ⟨hκ, p, hp, hpk, fun z hz => hκz z ?_⟩⟩
    rw [Multiset.mem_toFinset, mem_roots hp.ne_zero]
    exact hz
  choose κ hκ using hk
  exact ⟨ContAut.continuous_of_isOpen_stab E N u hu.level, leftInv hu hcen, κ, fun r h1 h2 => (hκ r h1 h2).1,
    bnd_of' hu hcen κ fun r h1 h2 => (hκ r h1 h2).2⟩

theorem intBnd : IntBnd := by
  intro E _ _ _ N H hc h0 hl m hm hB
  obtain ⟨_, hS, hL, _⟩ := dict_holds E N
  set φ : GA E N → ℂ := fun g => ((Real.sqrt (H g) : ℝ) : ℂ) with hφ
  have hφc : Continuous φ := Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hc)
  have hφB : An.Bnd φ (fun r => m r / 2) := by
    intro ω hω hωB t₀ Q hQ
    obtain ⟨C, hC⟩ := hB ω hω hωB t₀ Q hQ
    refine ⟨Real.sqrt (max C 0), fun b hb x hx q hq => ?_⟩
    have h1 := hC b hb x hx q hq
    rw [Complex.norm_real, Real.norm_of_nonneg (h0 _)] at h1
    set S := ∑ r ∈ Finset.range N, m r * An.sr x r with hSdef
    have e2 : ∑ r ∈ Finset.range N, m r / 2 * An.sr x r = S / 2 := by
      rw [hSdef, Finset.sum_div]
      exact Finset.sum_congr rfl fun r _ => by ring
    have e : Real.exp (∑ r ∈ Finset.range N, m r / 2 * An.sr x r) = Real.sqrt (Real.exp S) := by
      rw [e2]
      conv_rhs => rw [show S = S / 2 + S / 2 by ring]
      rw [Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
    have h2 : H (b * An.tor E x * q) ≤ max C 0 * Real.exp S :=
      h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    calc ‖φ (b * An.tor E x * q)‖ = Real.sqrt (H (b * An.tor E x * q)) := by
          rw [hφ, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt (max C 0 * Real.exp S) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt (max C 0) * Real.sqrt (Real.exp S) := Real.sqrt_mul (le_max_right _ _) _
      _ = _ := by rw [e]
  have hκ : ∀ r, 0 < r → r < N → m r / 2 < An.rho E N r := fun r h1 h2 => by
    have := hm r h1 h2
    linarith
  have hslab := GlobalTheory.CompanionTheory.SlabGlue.slabGlue boxvol_holds E N Measure.haar φ (fun r => m r / 2) hφc hφB hκ
  have hfd := isFundamentalDomain_stdDom (latticeGL E N) (Measure.haar : Measure (GA E N))
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := GroundTheory.Automorphic.Reduction.exists_siegelSet (K := E) N
  have : MeasurableConstSMul (latticeGL E N) (GA E N) := ⟨fun γ => measurable_const_mul (γ : GA E N)⟩
  have : SMulInvariantMeasure (latticeGL E N) (GA E N) (Measure.haar : Measure (GA E N)) :=
    ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have hle := JSqIntGlue.setLIntegral_le_of_cover hfd (S := An.slab ω (max 0 (-Real.log t)))
    (fun g => by
      obtain ⟨γ, hγ, h⟩ := JSqIntGlue.exists_mem_slab hS hL ht hsieg g
      exact ⟨⟨γ, hγ⟩, h⟩) (fun g => ENNReal.ofReal (H g)) (fun γ g => by
      show ENNReal.ofReal (H (γ.1 * g)) = ENNReal.ofReal (H g)
      rw [hl γ.1 γ.2 g])
  have e : ∀ g, ‖φ g‖ₑ ^ 2 = ENNReal.ofReal (H g) := fun g => by
    show ‖((Real.sqrt (H g) : ℝ) : ℂ)‖ₑ ^ 2 = _
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt (h0 g)]
  simp only [e] at hslab
  exact hle.trans_lt (hslab ω hω hωB _)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.UntwExp

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux.Tw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

omit [IsCMField E] in
theorem re_tw {z : ℂ} (hz : z.re = 0) : (z / (N * (Module.finrank ℚ E : ℂ))).re = 0 := by
  rw [Complex.div_re]
  simp [hz]

theorem untw_cen (hN : 0 < N) {z : ℂ} {φ : Sm E N}
    (hc : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = Complex.exp (z * t) * φ.1 g) (t : ℝ) (g : GA E N) :
    (mulChi N (Model.absC E (-(z / (N * (Module.finrank ℚ E : ℂ))))) φ).1 (splitCentre E N t * g) =
      (mulChi N (Model.absC E (-(z / (N * (Module.finrank ℚ E : ℂ))))) φ).1 g := by
  have hd : (Module.finrank ℚ E : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  set w := z / (N * (Module.finrank ℚ E : ℂ)) with hw
  have hcd : ∀ t : ℝ, ((chiDet N (Model.absC E (-w)) (splitCentre E N t) : ℂˣ) : ℂ) = Complex.exp (-(z * t)) := by
    intro t
    rw [ExponentTwist.splitCentre_eq, ExponentTwist.chiDet_aT le_rfl]
    congr 1
    rw [hw]
    field_simp
  rw [mulChi_apply, mulChi_apply, hc t g, map_mul, Units.val_mul, hcd t]
  have e : Complex.exp (z * t) * Complex.exp (-(z * t)) = 1 := by
    rw [← Complex.exp_add]; simp
  linear_combination (φ.1 g * ((chiDet N (Model.absC E (-w)) g : ℂˣ) : ℂ)) * e

theorem untw_exp {z : ℂ} (hz : z.re = 0) {φ : Sm E N} (hA : IsAutForm φ) (r : ℕ) (hr : 0 < r) (hrN : r < N) (c : ℂ)
    (hc : c ∈ Exp r (mulChi N (Model.absC E (-(z / (N * (Module.finrank ℚ E : ℂ))))) φ).1) :
    ∃ c' ∈ Exp r φ.1, pE E N r c = pE E N r c' := by
  have hd : (Module.finrank ℚ E : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set w := z / (N * (Module.finrank ℚ E : ℂ)) with hw
  have h1 := expTw_holds E N φ (-w) hA r hr hrN c hc
  refine ⟨_, h1, ?_⟩
  have e : -w * (r : ℂ) * (Module.finrank ℚ E : ℂ) = (((-(r : ℝ) / N) : ℝ) : ℂ) * z := by
    rw [hw]; push_cast; field_simp
  have hre : (c - -w * (r : ℂ) * (Module.finrank ℚ E : ℂ)).re = c.re := by
    rw [e, Complex.sub_re, Complex.re_ofReal_mul, hz, mul_zero, sub_zero]
  unfold pE
  rw [hre]

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux.Tw

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

open Tw ParabolicProjection in
theorem leaf_of (hC : Core) (hP : GrowPHolds) : Leaf := by
  intro E _ _ _ N τ hN U hU φ hφU hneg hφ0
  obtain ⟨⟨hst, hA⟩, -, hNP, ⟨z, hz, hcent⟩, -⟩ := hU
  have aut_tw {a : ℕ} {ψ : Sm E a} (h : IsAutForm ψ) (χ : HChar E) :
      IsAutForm (mulChi a χ ψ) := by
    exact {
      left γ g := by simp [h.left, chiDet_ratGL]
      level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
        ((h.level.inter (isOpen_ker_chiDet χ)).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
          have h1 : rt E a (finGL E a k) ψ = ψ := hk.1
          have h2 : chiDet a χ (finGL E a k) = 1 := hk.2
          change rt E a (finGL E a k) _ = _
          rw [rt_mulChi, h1, h2, Units.val_one, one_smul]
      kfin := by
        have := h.kfin
        refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k ψ)).map
          (GlobalTheory.CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
        rintro _ ⟨k, rfl⟩
        exact ⟨_, Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩), (rt_mulChi χ _ ψ).symm⟩
      zfin := by
        have := h.zfin
        refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z ψ) ''
          Zalg E a)).map (GlobalTheory.CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨z', h1, h2⟩ := Zalg_mulChi χ hz
        exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 ψ).symm⟩
      growth g := by
        obtain ⟨C, N, h1⟩ := h.growth g
        obtain ⟨C', N', h2⟩ := chiDet_growth (a := a) χ
        refine ⟨C * (‖((chiDet a χ g : ℂˣ) : ℂ)‖ * C'), N + N', fun y => ?_⟩
        rw [mulChi_apply, map_mul, Units.val_mul, norm_mul, norm_mul]
        refine (mul_le_mul (h1 y) (mul_le_mul_of_nonneg_left (h2 y) (norm_nonneg _)) (by positivity)
          ((norm_nonneg _).trans (h1 y))).trans_eq ?_
        ring }
  set w := z / (N * (Module.finrank ℚ E : ℂ)) with hw
  have hU'st : _root_.GlobalTheory.CuspRep.IsStable (tw U (-w)) := isStable_tw hst (-w)
  have hU'A : ∀ χ ∈ tw U (-w), IsAutForm χ := by
    rintro _ ⟨ψ, hψ, rfl⟩
    exact aut_tw (hA ψ hψ) _
  have hU'P : ∀ χ ∈ tw U (-w), GrowP χ.1 := by
    rintro _ ⟨ψ, hψ, rfl⟩
    refine hP E N _ (aut_tw (hA ψ hψ) _) (untw_cen hN (hcent ψ hψ)) fun r hr hrN c hc => ?_
    obtain ⟨c', hc', e⟩ := untw_exp hz (hA ψ hψ) r hr hrN c hc
    rw [e]
    exact hNP ψ hψ r hr hrN c' hc'
  have hφ'A2 : mulChi N (Model.absC E (-w)) φ ∈ A2 E N := by
    refine Submodule.subset_span ⟨aut_tw (hA φ hφU) _, sqIntCrit_holds E N _ (aut_tw (hA φ hφU) _)
      (untw_cen hN (hcent φ hφU)) fun r hr hrN c hc => ?_⟩
    obtain ⟨c', hc', e⟩ := untw_exp hz (hA φ hφU) r hr hrN c hc
    rw [e]
    exact hneg r hr hrN c' hc'
  have hφ'0 : mulChi N (Model.absC E (-w)) φ ≠ 0 := by
    rw [Ne, LinearEquiv.map_eq_zero_iff]; exact hφ0
  obtain ⟨V, p, hV, hpV, hpe, hp0⟩ :=
    hC E N (tw U (-w)) hU'st hU'A hU'P _ ⟨φ, hφU, rfl⟩ hφ'A2 hφ'0
  have hUle : ∀ ψ ∈ U, ψ ∈ tw (tw U (-w)) w := fun ψ hψ => ⟨_, ⟨ψ, hψ, rfl⟩, mulChi_absC_neg' N w ψ⟩
  refine ⟨.leaf V w, twMap N w p, Or.inr ⟨hN, hV, re_tw hz⟩, hN,
    fun o ψ hψ => twMap_equiv hU'st hpe o ψ (hUle ψ hψ), fun ψ hψ => twMap_mem hpV ψ (hUle ψ hψ), ?_⟩
  rw [twMap_apply, Ne, LinearEquiv.map_eq_zero_iff]
  exact hp0

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.LeafHolds2

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

open Leaf2Aux in
theorem leaf_holds2 : Leaf :=
  leaf_of (core_of (pairLin_of intBnd) pairRt (pairLie_of intBnd) growQHolds) growPHolds

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz
end
end
