module

public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.CompSt
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.LowSt
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.TubeSt
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.BoxExistence.ExistsBox
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ConstantSupremum.Tube0
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGensModNsmulOfFgNumberFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepsModKM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModRepsCardLeStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.LevelStabilisers.MemStabOfLev
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.MeasureSumBounds.SumMuFLe
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ProductMapEquality.PiCdEqMap
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.UpperFactors.FactorUpper

-- Source module: Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.FormalDegreeRankTwo.FinrankEqTwoFdeg

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open GlobalTheory.CovTop.VolUp
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.Tam.Z

theorem finrank_eq_two_fdeg (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Module.finrank ℚ E = 2 * fdeg E := by
  have h := NumberField.IsTotallyComplex.finrank (K := E)
  rw [fdeg, h]
  omega

theorem one_le_dE (E : Type) [Field E] [NumberField E] : 1 ≤ dE E := by
  rw [dE]
  have h0 := NumberField.discr_ne_zero E
  have h : (1 : ℤ) ≤ |NumberField.discr E| := Int.one_le_abs h0
  exact_mod_cast h

theorem massLev2_eq (E : Type) [Field E] [NumberField E] (r M : ℕ) :
    massLev2 E r M = (M : ℝ) ^ (Module.finrank ℚ E * r ^ 2) * 15 ^ (Module.finrank ℚ E * r ^ 2) *
      (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (r : ℝ) ^ 4 *
        (dE E ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^ (3 * Module.finrank ℚ E * r ^ 2) := rfl

theorem log_consts : 2 * Real.log 15 + 6 * (Real.log 3 + 2 * Real.log 2) ≤ 21 := by
  have hx : (0 : ℝ) < 15 ^ 2 * (3 * 2 ^ 2) ^ 6 := by norm_num
  have heq : 2 * Real.log 15 + 6 * (Real.log 3 + 2 * Real.log 2) =
      Real.log (15 ^ 2 * (3 * 2 ^ 2) ^ 6) := by
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  rw [heq, Real.log_le_iff_le_exp hx]
  have he : (2.7 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h21 : Real.exp 1 ^ 21 = Real.exp 21 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [← h21]
  calc (15 : ℝ) ^ 2 * (3 * 2 ^ 2) ^ 6 ≤ 2.7 ^ 21 := by norm_num
    _ ≤ Real.exp 1 ^ 21 := pow_le_pow_left₀ (by norm_num) he 21

end MainStatements.Tam.Z

namespace MainStatements.Tam

end MainStatements.Tam

theorem MainStatements.Tam.size : SizeSt := by
  unfold MainStatements.Tam.SizeSt
  intro E _ _ _ r M L hr hM hL hfr hMl hd
  have hn := MainStatements.Tam.Z.finrank_eq_two_fdeg E
  have hd1 := MainStatements.Tam.Z.one_le_dE E
  have hc := MainStatements.Tam.Z.log_consts
  rw [MainStatements.Tam.Z.massLev2_eq]
  set n := Module.finrank ℚ E with hn_def
  set f := fdeg E with hf_def
  have hnpos' : 0 < n := Module.finrank_pos
  have hf1 : 1 ≤ f := by omega
  have hnR : (n : ℝ) = 2 * f := by exact_mod_cast hn
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf1
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hnpos : (0 : ℝ) < n := by rw [hnR]; linarith
  have hrpos : (0 : ℝ) < r := by linarith
  have hfpos : (0 : ℝ) < f := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  have hdpos : 0 < dE E := by linarith
  set X := dE E ^ ((1 : ℝ) / (n : ℝ)) with hX_def
  have hX1 : 1 ≤ X := Real.one_le_rpow hd1 (by positivity)
  have hXpos : 0 < X := by linarith
  have hlogX : Real.log X = (1 / (n : ℝ)) * Real.log (dE E) := Real.log_rpow hdpos _
  have hnX : (n : ℝ) * Real.log X = Real.log (dE E) := by
    rw [hlogX]
    field_simp
  set B : ℝ := 3 * ((n : ℝ) ^ 2 * (r : ℝ) ^ 4 * X ^ 2) with hB_def
  have hn1 : (1 : ℝ) ≤ n := by rw [hnR]; linarith
  have hB1 : 1 ≤ B := by
    have h1 : 1 ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
    have h2 : 1 ≤ (r : ℝ) ^ 4 := one_le_pow₀ (by linarith)
    have h3 : 1 ≤ X ^ 2 := one_le_pow₀ hX1
    have h4 : 1 ≤ (n : ℝ) ^ 2 * (r : ℝ) ^ 4 * X ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) h3
    rw [hB_def]
    linarith
  have hBpos : 0 < B := by linarith
  have h15 : (1 : ℝ) ≤ 15 := by norm_num
  constructor
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hMR) (one_le_pow₀ h15)) (one_le_pow₀ hB1)
  · have ha : (n : ℝ) ^ 2 ≠ 0 := (pow_pos hnpos 2).ne'
    have hb : (r : ℝ) ^ 4 ≠ 0 := (pow_pos hrpos 4).ne'
    have hx : X ^ 2 ≠ 0 := (pow_pos hXpos 2).ne'
    have hab : (n : ℝ) ^ 2 * (r : ℝ) ^ 4 ≠ 0 := mul_ne_zero ha hb
    have habx : (n : ℝ) ^ 2 * (r : ℝ) ^ 4 * X ^ 2 ≠ 0 := mul_ne_zero hab hx
    have hlogB : Real.log B = Real.log 3 + 2 * Real.log n + 4 * Real.log r + 2 * Real.log X := by
      rw [hB_def, Real.log_mul (by norm_num) habx, Real.log_mul hab hx, Real.log_mul ha hb,
        Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast
      ring
    have hm1 : (M : ℝ) ^ (n * r ^ 2) ≠ 0 := (pow_pos hMpos _).ne'
    have hm2 : (15 : ℝ) ^ (n * r ^ 2) ≠ 0 := (pow_pos (by norm_num) _).ne'
    have hm3 : B ^ (3 * n * r ^ 2) ≠ 0 := (pow_pos hBpos _).ne'
    rw [Real.log_mul (mul_ne_zero hm1 hm2) hm3, Real.log_mul hm1 hm2, Real.log_pow, Real.log_pow,
      Real.log_pow, hlogB]
    have hlogn : Real.log n = Real.log 2 + Real.log f := by
      rw [hnR, Real.log_mul (by norm_num) hfpos.ne']
    have hlfr : Real.log ((f : ℝ) * r) = Real.log f + Real.log r :=
      Real.log_mul hfpos.ne' hrpos.ne'
    rw [hlfr] at hfr
    rw [hlogn]
    push_cast
    rw [hnR] at hnX ⊢
    have hlf : 0 ≤ Real.log f := Real.log_nonneg hfR
    have hK : 0 ≤ (f : ℝ) * r ^ 2 := by positivity
    have pa := mul_le_mul_of_nonneg_left hMl hK
    have pb := mul_le_mul_of_nonneg_left hc hK
    have pc := mul_le_mul_of_nonneg_left hfr hK
    have pd := mul_nonneg hK hlf
    have pe := mul_nonneg hK (by linarith : (0 : ℝ) ≤ L - 1)
    have pf := mul_nonneg hK (by linarith : (0 : ℝ) ≤ L)
    have ph : (r : ℝ) ^ 2 * (2 * f * Real.log X) ≤ (r : ℝ) ^ 2 * (4 * f * L) := by
      rw [hnX]
      exact mul_le_mul_of_nonneg_left hd (by positivity)
    nlinarith [pa, pb, pc, pd, pe, pf, ph]

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.InverseMultiplication.IsKMInvMul

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open GlobalTheory.CovTop.VolUp
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.Tam.I

open GlobalTheory.UCls.IdxK

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem isKM_inv_mul' {n M : ℕ} {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)}
    {g s : Matrix (Fin n) (Fin n) (RA F E)} (hg : GlobalTheory.UCls.IsKM c G L 1 g) (hs : GlobalTheory.UCls.IsKM c G L 1 s)
    (hgs : ∀ x ∈ GlobalTheory.AdLat.hat F L, ∃ y ∈ GlobalTheory.AdLat.hat F L, g *ᵥ x - s *ᵥ x = M • y) :
    GlobalTheory.UCls.IsKM c G L M (s⁻¹ * g) := by
  have hsu : IsUnit s.det := hs.1.1
  have hss : ∀ v, s *ᵥ (s⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hsu, Matrix.one_mulVec]
  have hss' : ∀ v, s⁻¹ *ᵥ (s *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hsu, Matrix.one_mulVec]
  have into : ∀ x ∈ GlobalTheory.AdLat.hat F L, s *ᵥ x ∈ GlobalTheory.AdLat.hat F L := by
    intro x hx
    obtain ⟨y, hy, h⟩ := hs.2.1 x hx
    rw [one_smul] at h
    rw [show s *ᵥ x = x + y by rw [← h]; abel]
    exact add_mem hx hy
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_nonsing_inv]
    exact (hsu.ringInverse).mul hg.1.1
  · intro x y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hs.1.2 (s⁻¹ *ᵥ (g *ᵥ x)) (s⁻¹ *ᵥ (g *ᵥ y)), hss, hss,
      hg.1.2]
  · intro x hx
    obtain ⟨y, hy, h⟩ := hgs x hx
    obtain ⟨w, hw, rfl⟩ := hs.2.2 y hy
    refine ⟨w, hw, ?_⟩
    have h1 : g *ᵥ x = s *ᵥ (x + M • w) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, ← h]; abel
    rw [← Matrix.mulVec_mulVec, h1, hss']
    abel
  · intro x hx
    obtain ⟨y, hy, h⟩ := hg.2.2 (s *ᵥ x) (into x hx)
    exact ⟨y, hy, by rw [← Matrix.mulVec_mulVec, h, hss']⟩

end MainStatements.Tam.I

namespace MainStatements.Tam

open GlobalTheory.UCls.IdxK

theorem idx : IdxSt := by
  intro E _ _ _ r M G Λ hM hSD
  classical
  have hFG : Λ.FG := hSD.2.2.1
  obtain ⟨e, heΛ, he⟩ := GlobalTheory.T.exists_gens_mod_nsmul_of_fg_numberField E r M Λ hM hFG
  obtain ⟨T, hTc, hTΛ, hT⟩ := GlobalTheory.T.exists_reps_mod_lattice_card_le E r M Λ hM hFG
  have hLo : ∀ o : 𝓞 E, ∀ x ∈ (Λ : Set (Fin r → E)), o • x ∈ (Λ : Set (Fin r → E)) :=
    fun o x hx => Λ.smul_mem o hx
  have hLb : ∀ b : 𝓞 (maximalRealSubfield E), ∀ x ∈ (Λ : Set (Fin r → E)),
      algebraMap (maximalRealSubfield E) E (b : maximalRealSubfield E) • x ∈ (Λ : Set (Fin r → E)) := by
    intro b x hx
    have hi : IsIntegral ℤ (algebraMap (maximalRealSubfield E) E (b : maximalRealSubfield E)) :=
      b.2.map (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)
    exact Λ.smul_mem (⟨_, hi⟩ : 𝓞 E) hx
  have hQ : ∀ z ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin r → E)), ∃ t ∈ T,
      ∃ y ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin r → E)), z = GlobalTheory.AdLat.fv _ t + M • y := by
    intro z hz
    obtain ⟨t0, ht0, y0, hy0, rfl⟩ := hat_approx hM hLb Λ.zero_mem (fun x hx y hy => Λ.add_mem hx hy)
      (fun x hx => Λ.neg_mem hx) z hz
    obtain ⟨t, ht, y1, hy1, rfl⟩ := hT t0 ht0
    refine ⟨t, ht, GlobalTheory.AdLat.fv _ y1 + y0, add_mem (fv_mem hy1) hy0, ?_⟩
    rw [fv_add, fv_nsmul, smul_add, add_assoc]
  have into : ∀ g, GlobalTheory.UCls.IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 1 g →
      ∀ x ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin r → E)),
        g *ᵥ x ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) := by
    intro g hg x hx
    obtain ⟨y, hy, h⟩ := hg.2.1 x hx
    rw [one_smul] at h
    rw [show g *ᵥ x = x + y by rw [← h]; abel]
    exact add_mem hx hy
  let K1 := {g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E) //
    GlobalTheory.UCls.IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 1 g}
  have hex : ∀ g : K1, ∀ i, ∃ t ∈ T, ∃ y ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin r → E)),
      g.1 *ᵥ GlobalTheory.AdLat.fv _ (e i) = GlobalTheory.AdLat.fv _ t + M • y :=
    fun g i => hQ _ (into g.1 g.2 _ (fv_mem (heΛ i)))
  choose τ hτT yy hyy hτ using hex
  let σ : (Fin r → Fin r → E) → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E) :=
    fun t => if h : ∃ g : K1, τ g = t then h.choose.1 else 1
  refine ⟨(Fintype.piFinset fun _ : Fin r => T).image σ, ?_, ?_⟩
  · calc _ ≤ (Fintype.piFinset fun _ : Fin r => T).card := Finset.card_image_le
      _ = T.card ^ r := by simp
      _ ≤ (M ^ (2 * fdeg E * r)) ^ r := Nat.pow_le_pow_left hTc r
      _ = _ := by rw [← pow_mul]; ring_nf
  · intro g hg
    let g' : K1 := ⟨g, hg⟩
    have hex' : ∃ g'' : K1, τ g'' = τ g' := ⟨g', rfl⟩
    have hσ : σ (τ g') = hex'.choose.1 := dif_pos hex'
    have hsτ : τ hex'.choose = τ g' := hex'.choose_spec
    set s' := hex'.choose with hs'
    refine ⟨s'.1, Finset.mem_image.2 ⟨τ g', Fintype.mem_piFinset.2 fun i => hτT g' i, hσ⟩, s'.2,
      s'.1⁻¹ * g, ?_, ?_⟩
    · refine MainStatements.Tam.I.isKM_inv_mul' hg s'.2 ?_
      refine cong_of_gens hLo e he g s'.1 (into g hg) (into s'.1 s'.2) fun i => ?_
      refine ⟨yy g' i - yy s' i, sub_mem (hyy g' i) (hyy s' i), ?_⟩
      have h1 := hτ g' i
      have h2 := hτ s' i
      rw [hsτ] at h2
      change g *ᵥ GlobalTheory.AdLat.fv _ (e i) = _ at h1
      rw [h1, h2, smul_sub]
      abel
    · rw [← mul_assoc, Matrix.mul_nonsing_inv _ s'.2.1.1, one_mul]

end MainStatements.Tam

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ConstantSupremum.Imports

section

@[expose] public section

namespace MainStatements.Tam.Plug

theorem low : LowSt := MainStatements.Tam.low MainStatements.Tam.vol MainStatements.Tam.stab MainStatements.Tam.num

theorem comp : CompSt := MainStatements.Tam.comp (tube0 MainStatements.Tam.vol MainStatements.Tam.stab MainStatements.Tam.idx) MainStatements.Tam.num

theorem size : SizeSt := MainStatements.Tam.size

end MainStatements.Tam.Plug
end
end
