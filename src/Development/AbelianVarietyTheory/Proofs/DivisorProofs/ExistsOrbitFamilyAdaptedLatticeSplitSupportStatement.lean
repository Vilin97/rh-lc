module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryCongruentLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalUnitaryMoveSelfDualToSplitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortRuleChangeMat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalUnitarySplitDenominator
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StandardHermitianFormHostFieldInhabitant
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortRuleChangeOfCongr
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FixesDatumOfCongAt
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLatticeStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_adelic_unitary_translate_standardLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n M : ℕ) (Λ : GenLat E n), 0 < M → Λ.Unimod → Λ.TrivAt M → ∃ g : GL (Fin n) (RA (maximalRealSubfield E) E), IsUnA (IsCMField.complexConj E) (1 : Matrix (Fin n) (Fin n) E) g.1 ∧ (Λ.La : Set (Fin n → E)) = latOf (maximalRealSubfield E) g.1 (stdLat E n : Set (Fin n → E)) ∧ ∀ D : ℕ, 0 < D → CongAtA (maximalRealSubfield E) (stdLat E n) M D g.1 := by
  first | exact @GlobalTheory.AdelTranslate.exists_adelic_translate | exact GlobalTheory.AdelTranslate.exists_adelic_translate | (intros; apply GlobalTheory.AdelTranslate.exists_adelic_translate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalUnitarySplitDenominatorStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_rational_unitary_split_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N : ℕ), IsUnA c G g.1 → 0 < N → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAtA F L N N (fm F γ.1 * g.1) ∧ ∃ s : 𝓞 E, SplitOff c N s ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • ((fm F γ.1 * g.1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) ∧ ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • (((g⁻¹).1 * fm F (γ⁻¹).1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) := by
  first | exact @GlobalTheory.UnRep.LatForm.exists_rep_split_denominator | exact GlobalTheory.UnRep.LatForm.exists_rep_split_denominator | (intros; apply GlobalTheory.UnRep.LatForm.exists_rep_split_denominator <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StandardHermitianFormHostFieldInhabitantStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.standardHermitianForm_hostField_inhabitant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n : ℕ), IsHermForm (IsCMField.complexConj E) (1 : Matrix (Fin n) (Fin n) E) ∧ Module.finrank (maximalRealSubfield E) E = 2 ∧ (stdLat E n).FG ∧ Submodule.span E (stdLat E n : Set (Fin n → E)) = ⊤ ∧ SplitOff (IsCMField.complexConj E) 1 H.w0 ∧ ¬ IsUnit H.w0 ∧ (∀ P : Ideal (𝓞 E), P.IsPrime → (Moved (IsCMField.complexConj E) P ↔ P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P)) ∧ ∀ γ : Matrix (Fin n) (Fin n) E, IsUnE (IsCMField.complexConj E) 1 γ ↔ ∀ i j, ∑ b, (IsCMField.complexConj E) (γ b i) * γ b j = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.UnRep.StdInhab.main | exact GlobalTheory.UnRep.StdInhab.main | (intros; apply GlobalTheory.UnRep.StdInhab.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAdaptedCongr

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct Matrix

namespace GlobalTheory.AdaptCongr

open GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.UnRep.Move

theorem exists_move_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n M bad : ℕ) (Λ : GenLat E n), 0 < M → 0 < bad → Λ.Unimod → Λ.TrivAt M → ∃ (γ : GL (Fin n) E) (Λ' : GenLat E n), IsUnE (IsCMField.complexConj E) 1 γ.1 ∧ CongAt (stdLat E n) M M γ.1 ∧ (∀ v, v ∈ Λ.La ↔ γ.1 *ᵥ v ∈ Λ'.La) ∧ Λ'.Unimod ∧ ∃ s : 𝓞 E, s ≠ 0 ∧ Ideal.span {s} • Λ'.La ≤ stdLat E n ∧ Ideal.span {s} • stdLat E n ≤ Λ'.La ∧ (∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P ∧ ((bad * M : ℕ) : 𝓞 E) ∉ P) ∧ ∃ k : ℕ, k.Coprime (bad * M) ∧ Ideal.span {(k : 𝓞 E)} • Λ'.La ≤ stdLat E n ∧ Ideal.span {(k : 𝓞 E)} • stdLat E n ≤ Λ'.La := by
  intro E _ _ _ H n M bad Λ hM hbad hU hT
  obtain ⟨hherm, hrk, hfg, hsp, -, -, hmov, hun⟩ := GlobalTheory.T.standardHermitianForm_hostField_inhabitant E H n
  obtain ⟨g, hg, hΛ, hgc⟩ := GlobalTheory.T.exists_adelic_unitary_translate_standardLattice E H n M Λ hM hU hT
  obtain ⟨γ, hγ, ⟨t₁, ht₁, hc₁⟩, s, ⟨hs0, hs⟩, hint⟩ := GlobalTheory.T.exists_rational_unitary_split_denominator (maximalRealSubfield E) E
    (IsCMField.complexConj E) n 1 hherm hrk (stdLat E n) hfg hsp g (bad * M) hg (Nat.mul_pos hbad hM)
  obtain ⟨t₂, ht₂, hc₂⟩ := hgc M hM
  have hrat := (hat_rational_points_and_approx (maximalRealSubfield E) E n (stdLat E n) hfg hsp).1
  have hmem : ∀ v, v ∈ Λ.La ↔ ∃ z ∈ hat (maximalRealSubfield E) (stdLat E n : Set (Fin n → E)),
      g.1 *ᵥ z = fv (maximalRealSubfield E) v := by
    intro v
    rw [← SetLike.mem_coe, hΛ]
    rfl
  have hinv : ∀ v : Fin n → E, (γ⁻¹).1 *ᵥ (γ.1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hinv' : ∀ v : Fin n → E, γ.1 *ᵥ ((γ⁻¹).1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  let Λ' : GenLat E n := ⟨Λ.La.comap ((Matrix.mulVecLin (γ⁻¹).1).restrictScalars (𝓞 E))⟩
  have hΛ' : ∀ v, v ∈ Λ'.La ↔ (γ⁻¹).1 *ᵥ v ∈ Λ.La := fun v => Iff.rfl
  have hmove : ∀ v, v ∈ Λ.La ↔ γ.1 *ᵥ v ∈ Λ'.La := fun v => by rw [hΛ', hinv]
  have hsE : ∀ v : Fin n → E, s • v = (s : E) • v := fun v => rfl
  have h1 : ∀ v ∈ Λ'.La, s • v ∈ stdLat E n := by
    intro v hv
    obtain ⟨z, hz, hzv⟩ := (hmem _).1 ((hΛ' v).1 hv)
    have := (hint z hz).1
    rw [← Matrix.mulVec_mulVec, hzv, ← fv_mulVec, hinv', ← fv_smul] at this
    rw [hsE]
    exact (hrat _).1 this
  have h2 : ∀ v ∈ stdLat E n, s • v ∈ Λ'.La := by
    intro v hv
    have := (hint _ ((hrat v).2 hv)).2
    rw [hΛ', hmem]
    refine ⟨_, this, ?_⟩
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mul, ← fv_mulVec, ← fv_smul, hsE, Matrix.mulVec_smul]
  obtain ⟨k, hk, hsk⟩ := exists_nat_coprime s (bad * M) fun P hP hsP => (hs P hP hsP).2
  refine ⟨γ, Λ', hγ, ?_, hmove, unimod_move γ hγ Λ Λ' hmove hU, s, hs0, (span_smul_le _ _ _).2 h1,
    (span_smul_le _ _ _).2 h2, fun P hP hsP => ⟨(hmov P hP).1 (hs P hP hsP).1, (hs P hP hsP).2⟩, k, hk,
    (span_smul_le _ _ _).2 fun v hv => smul_mem_of_dvd hsk (h1 v hv),
    (span_smul_le _ _ _).2 fun v hv => smul_mem_of_dvd hsk (h2 v hv)⟩
  · obtain ⟨j, hj, -, hj2⟩ := hT
    refine ⟨t₁ * t₂ * j, (ht₁.coprime_mul_left_right.mul_left ht₂).mul_left hj, fun v hv => ?_⟩
    have hjv : j • v ∈ Λ.La := by
      have := (span_smul_le _ _ _).1 hj2 v hv
      rwa [Nat.cast_smul_eq_nsmul] at this
    obtain ⟨z, hz, hzv⟩ := (hmem _).1 hjv
    obtain ⟨w₁, hw₁, e₁⟩ := hc₁ z hz
    obtain ⟨w₂, hw₂, e₂⟩ := hc₂ z hz
    have hME : (M : E) ≠ 0 := by exact_mod_cast hM.ne'
    have key : (t₁ * t₂ * j) • (γ.1 *ᵥ v - v) = M • ((M : E)⁻¹ • ((t₁ * t₂ * j) • (γ.1 *ᵥ v - v))) := by
      rw [← Nat.cast_smul_eq_nsmul E M, smul_smul, mul_inv_cancel₀ hME, one_smul]
    refine ⟨_, ?_, key⟩
    rw [← hrat]
    have e : fv (maximalRealSubfield E) ((M : E)⁻¹ • ((t₁ * t₂ * j) • (γ.1 *ᵥ v - v)))
        = (t₂ * bad) • w₁ - t₁ • w₂ := by
      refine nsmul_cancel _ hM ?_
      rw [← cap_fv_nsmul, ← key, mul_smul, smul_sub j, ← Matrix.mulVec_smul, cap_fv_nsmul, fv_sub, fv_mulVec,
        ← hzv, Matrix.mulVec_mulVec]
      have a1 : M • ((t₂ * bad) • w₁) = t₂ • ((bad * M) • w₁) := by
        rw [smul_smul, smul_smul]; congr 1; ring
      have a2 : M • (t₁ • w₂) = t₁ • (M • w₂) := smul_comm _ _ _
      rw [smul_sub M, a1, a2, ← e₁, ← e₂, smul_smul, smul_smul, mul_comm t₂ t₁, ← smul_sub, sub_sub_sub_cancel_right]
    rw [e]
    exact sub_mem (nsmul_mem hw₁ _) (nsmul_mem hw₂ _)

end GlobalTheory.AdaptCongr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrbitFamilyAdaptedLatticeSplitSupport

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.OrbitAdapt

section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out Formalism.MainNotions.WeightAlgebra GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence GlobalTheory.ShortMove

theorem exists_step_int (D : D7) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (n : ℕ) (hev : Even n)
    (hb : 0 < badN D) (Λ : GenLat D.host.E n) (N : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (hU : Λ.Unimod) (hT : Λ.TrivAt (badN D))
    (hM : Λ.TrivAt (T.dδ j n).l₂.M) (hN : Λ.LevOK N (T.dδ j n).l₂.M) (hP : P ∈ harmL T.Q.c Λ a) (p : ℕ)
    (hp : 0 < p) :
    ∃ (Λ₁ : GenLat D.host.E n) (N₁ : ℕ) (P₁ : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (ζ : T.Q.c.F),
      Λ₁.Unimod ∧ Λ₁.TrivAt (badN D * (T.dδ j n).l₂.M * p) ∧ Λ₁.LevOK N₁ (T.dδ j n).l₂.M ∧ P₁ ∈ harmL T.Q.c Λ₁ a ∧
      ζ ≠ 0 ∧ (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      (∀ (x0 : Fin n → (T.Q.Dw j).La) (f : Rul (T.Q.Xo j) T.Q.c),
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x0 P f →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ₁ N₁ x0 P₁ (ζ • f)) := by
  have hBM := GlobalTheory.ShortChange.trivAt_mul hT hM
  have hMpos : 0 < (T.dδ j n).l₂.M := by have := (T.dδ j n).l₂.three_le; omega
  obtain ⟨γ, Λ', hγ, hc, hmove, hU', s, -, -, -, -, k, hk, hk1, hk2⟩ :=
    GlobalTheory.AdaptCongr.exists_move_split D.host.E T.Q.H n _ p Λ (Nat.mul_pos hb hMpos) hp hU hBM
  have h2b : 2 ∣ badN D := by
    unfold badN
    exact ((D.host.two_dvd_QS.mul_right _).mul_right _).mul_right _
  have hg : IsUnitaryM γ.1 := by
    refine Matrix.ext fun i l => ?_
    have := hγ (Pi.single l 1) (Pi.single i 1)
    rw [GlobalTheory.UnRep.Move.hermE_one, GlobalTheory.UnRep.Move.hermE_one] at this
    simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
    simp only [adjM, Matrix.mul_apply, Matrix.of_apply, this, Matrix.one_apply, Pi.single_apply]
    by_cases h : i = l
    · subst h; simp [apply_ite (IsCMField.complexConj D.host.E)]
    · simp [h, apply_ite (IsCMField.complexConj D.host.E), Ne.symm h]
  have hinv' : ∀ v : Fin n → D.host.E, γ.1 *ᵥ ((γ⁻¹).1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  obtain rfl : Λ' = actLat γ.1 Λ := by
    cases Λ' with
    | mk L =>
      simp only [actLat, GenLat.mk.injEq]
      ext v
      constructor
      · intro hv
        exact ⟨_, (hmove _).2 (by rw [hinv']; exact hv), hinv' v⟩
      · rintro ⟨u, hu, rfl⟩
        exact (hmove u).1 hu
  have hkT : ∀ m, m ∣ p * (badN D * (T.dδ j n).l₂.M) → (actLat γ.1 Λ).TrivAt m := fun m hm =>
    ⟨k, hk.coprime_dvd_right hm, hk1, hk2⟩
  have hN₁ : (actLat γ.1 Λ).LevOK ((T.dδ j n).l₂.M * k) (T.dδ j n).l₂.M := by
    refine ⟨?_, dvd_mul_right _ _, ?_⟩
    · exact (T.dδ j n).l₂.odd.mul
        (Nat.coprime_two_right.1 (hk.coprime_dvd_right ((h2b.mul_right _).mul_left _)))
    · show _ ≤ (actLat γ.1 Λ).La ⊓ Formalism.L2.Pj.stdLat D.host.E n
      refine le_inf ((Submodule.smul_mono_left ?_).trans hk2) Submodule.smul_le_right
      refine Ideal.span_singleton_le_span_singleton.2 ?_
      rw [Nat.cast_mul]
      exact dvd_mul_left _ _
  obtain ⟨P₁, ζ, hP₁, hζ, hroot, hR⟩ := shortRule_change_mat D T hF j hj n Λ γ.1 _ a P hg
    (dvd_mul_left _ _) hc hev hU hU' hT (hkT _ ((dvd_mul_right _ _).mul_left _)) hM
    (hkT _ ((dvd_mul_left _ _).mul_left _)) hP
  exact ⟨actLat γ.1 Λ, _, P₁, ζ, hU', hkT _ (by rw [mul_comm]), hN₁, hP₁, hζ, hroot,
    fun x0 f h => hR x0 N _ f hN hN₁ h⟩

theorem exists_step_split_off (D : D7) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (V : Formalism.BasicNotions.TH.HSp D)
    (hg : V.gram = 1) (hL : Formalism.IndefR.Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank) (hev : Even V.rank) (hb : 0 < badN D)
    (p : ℕ) (hp : 0 < p) (Λ : GenLat D.host.E V.rank) (N : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) V.rank) T.Q.c.F) (hU : Λ.Unimod)
    (hT : Λ.TrivAt (badN D * (T.dδ j V.rank).l₂.M * p)) (hN : Λ.LevOK N (T.dδ j V.rank).l₂.M)
    (hP : P ∈ harmL T.Q.c Λ a) :
    ∃ (h : Formalism.L2.Theta.GA D V) (Λ' : GenLat D.host.E V.rank) (N' : ℕ)
      (P' : MvPolynomial (LtN (T.Q.Dw j) V.rank) T.Q.c.F) (ζ : T.Q.c.F),
      Formalism.IndefR.FWT.SplitOffBad V (badN D * (T.dδ j V.rank).l₂.M * p) h ∧
      (∀ w, w ∈ Λ'.La ↔ (fun b => star (w b)) ∈ Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V h)) ∧
      Λ'.Unimod ∧ Λ'.TrivAt (badN D) ∧ Λ'.TrivAt (T.dδ j V.rank).l₂.M ∧ Λ'.TrivAt p ∧
      Λ'.LevOK N' (T.dδ j V.rank).l₂.M ∧ P' ∈ harmL T.Q.c Λ' a ∧ ζ ≠ 0 ∧ (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      ∀ (x0 : Fin V.rank → (T.Q.Dw j).La) (f : Rul (T.Q.Xo j) T.Q.c),
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j V.rank) Λ N x0 P f →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j V.rank) Λ' N' x0 P' (ζ • f) := by
  have hM0 : 0 < (T.dδ j V.rank).l₂.M := by have := (T.dδ j V.rank).l₂.three_le; omega
  have hpos : 0 < badN D * p * (T.dδ j V.rank).l₂.M := Nat.mul_pos (Nat.mul_pos hb hp) hM0
  have hT' : Λ.TrivAt (badN D * p * (T.dδ j V.rank).l₂.M) := by
    rwa [show badN D * p * (T.dδ j V.rank).l₂.M = badN D * (T.dδ j V.rank).l₂.M * p by ring]
  obtain ⟨gm, h, hgm, hc, hh, hs, e⟩ := GlobalTheory.T.exists_rationalUnitary_move_selfDual_to_split D V hg hL T.Q.H _ hpos Λ hU hT'
  have h2 : 2 ∣ badN D * p := by
    unfold badN
    exact dvd_mul_of_dvd_left (((D.host.two_dvd_QS.mul_right _).mul_right _).mul_right _) p
  obtain ⟨N', c1, c2, c3, c4, -⟩ := GlobalTheory.SplitReps.exists_conjLat V hg hL T.Q.H (T.dδ j V.rank).l₂ (badN D * p) h2 h hs
  rw [← e] at c1 c2 c3 c4
  have hcg := congAt_of_cols gm _ hc
  have hTb : Λ.TrivAt (badN D) := trivAt_of_dvd ⟨(T.dδ j V.rank).l₂.M * p, by ring⟩ hT
  have hTM : Λ.TrivAt (T.dδ j V.rank).l₂.M := trivAt_of_dvd ⟨badN D * p, by ring⟩ hT
  obtain ⟨P', ζ, hP', hζ, hroot, hR⟩ := shortRule_change_mat D T hF j hj V.rank Λ gm _ a P hgm
    (dvd_mul_left _ _) hcg hev hU c1 hTb (trivAt_of_dvd (dvd_mul_right _ _) c2) hTM c3 hP
  have hsp : Formalism.IndefR.FWT.SplitOffBad V (badN D * p * (T.dδ j V.rank).l₂.M) h :=
    GlobalTheory.SplitReps.splitOffBad_of_suppSplit V _ h hh hs
  refine ⟨h, actLat gm Λ, N', P', ζ, ?_, fun w => by rw [e]; rfl, c1, trivAt_of_dvd (dvd_mul_right _ _) c2, c3,
    trivAt_of_dvd (dvd_mul_left _ _) c2, c4, hP', hζ, hroot, fun x0 f hf => hR x0 N N' f hN c4 hf⟩
  rwa [show badN D * (T.dδ j V.rank).l₂.M * p = badN D * p * (T.dδ j V.rank).l₂.M by ring]

theorem splitOffBad_of_dvd (D : D7) (V : Formalism.BasicNotions.TH.HSp D) {a b : ℕ} (hab : a ∣ b) {h : Formalism.L2.Theta.GA D V}
    (hs : Formalism.IndefR.FWT.SplitOffBad V b h) : Formalism.IndefR.FWT.SplitOffBad V a h := by
  obtain ⟨h1, e', Q, h3, h4, h5⟩ := hs
  obtain ⟨c, rfl⟩ := hab
  refine ⟨h1, e', Q, h3, fun PP hP hbd => h4 PP hP ?_, h5⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hbd

end


open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence GlobalTheory.ShortMove in
set_option maxHeartbeats 1000000 in
theorem exists_adapted : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)) (U : Subgroup G) (lam : HeightOneSpectrum (𝓞 D.what₂.LL)) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)), IsOrbitFamily (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (badN D) (wtA (κ i)) (T.dδ ((i : ℕ) + 1) (κ i).n) (fun u : U => ℓ u) (fun u => ((f u).1 : T.R ((i : ℕ) + 1))) → ∃ (a : 𝓞 T.Q.c.F) (s : ℕ) (f' : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La), (s : 𝓞 D.what₂.LL) ∉ lam.asIdeal ∧ (∀ u, (s : T.Q.c.F) • ((f u).1 : T.R ((i : ℕ) + 1)) = (a : T.Q.c.F) • ((f' u).1 : T.R ((i : ℕ) + 1))) ∧ SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h ∧ (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) ∧ Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) ∧ Λ.Unimod ∧ Λ.TrivAt (badN D) ∧ Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧ Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧ AdmX (l := T.Q.l) true x₀ ∧ P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) ∧ ∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f' u).1 : T.R ((i : ℕ) + 1)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hk i hO ℓ U lam f hf
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hrk : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hn : (κ i).n = (Vc D i).rank := (fw.kap i (D.eTau.symm 1)).2.2.trans hrk.symm
  have hr : Odd D.R.r := by
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    have h2 := D.R.two_le_m
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have hev : Even (Vc D i).rank := hrk ▸ hr.add_odd D.R.t_odd
  have hV := hO.2.lift.std
  have hg : (Vc D i).gram = 1 := hV.1
  have hL : Bridge.hLat (Vc D i) 1 = Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank := hV.2
  rw [hn] at hf
  obtain ⟨Λ, N, x₀, P, x, hU, hTb, hTM, hN, hA, hP, hx⟩ := hf
  have hp := plc_prime lam
  have hq : 0 < Formalism.EigenvalueLevelCeiling.plc lam * (O i).bad () := Nat.mul_pos hp.pos (hO.2.bad ()).1
  obtain ⟨h, Λ', N', P', ζ, hs, hmem, hU', hTb', hTM', hTp, hN', hP', hζ, ⟨m, hm, hζm⟩, hR⟩ :
      ∃ (h : GA D (Vc D i)) (Λ' : GenLat D.host.E (Vc D i).rank) (N' : ℕ)
        (P' : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (ζ : T.Q.c.F),
        SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h ∧
        (∀ w, w ∈ Λ'.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) ∧
        Λ'.Unimod ∧ Λ'.TrivAt (badN D) ∧ Λ'.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧
        Λ'.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) ∧ Λ'.LevOK N' (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧
        P' ∈ harmL T.Q.c Λ' (wtA (κ i)) ∧ ζ ≠ 0 ∧ (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
        ∀ (x0 : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (g : Rul (T.Q.Xo ((i : ℕ) + 1)) T.Q.c),
          IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x0 P g →
          IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ' N' x0 P' (ζ • g) := by
    rcases Nat.eq_zero_or_pos (badN D) with hb | hb
    · rw [hb] at hTb
      obtain ⟨h1, h2, h3⟩ := zero_case D (Vc D i) hL Λ hTb
      exact ⟨1, Λ, N, P, 1, h2 _, h1, hU, h3 _, h3 _, h3 _, hN, hP, one_ne_zero, ⟨1, one_pos, one_pow _⟩,
        fun x0 g hg => by rwa [one_smul]⟩
    · obtain ⟨Λ₁, N₁, P₁, ζ₁, hU₁, hT₁, hN₁, hP₁, hζ₁, ⟨m₁, hm₁, e₁⟩, hR₁⟩ :=
        exists_step_int D T hT ((i : ℕ) + 1) hj _ hev hb Λ N (wtA (κ i)) P hU hTb hTM hN hP _ hq
      obtain ⟨h, Λ', N', P', ζ₂, d1, d2, d3, d4, d5, d6, d7, d8, hζ₂, ⟨m₂, hm₂, e₂⟩, hR₂⟩ :=
        exists_step_split_off D T hT _ hj (Vc D i) hg hL hev hb _ hq Λ₁ N₁ _ P₁ hU₁ hT₁ hN₁ hP₁
      refine ⟨h, Λ', N', P', ζ₂ * ζ₁, splitOffBad_of_dvd D _ ⟨Formalism.EigenvalueLevelCeiling.plc lam, by ring⟩ d1, d2, d3, d4, d5,
        trivAt_of_dvd (dvd_mul_right _ _) d6, d7, d8, mul_ne_zero hζ₂ hζ₁,
        ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, by rw [mul_pow, pow_mul' ζ₂, e₂, pow_mul ζ₁, e₁, one_pow, one_pow, one_mul]⟩,
        fun x0 g hg => ?_⟩
      rw [mul_smul]
      exact hR₂ x0 _ (hR₁ x0 g hg)
  have hint : IsIntegral ℤ (ζ ^ (m - 1)) :=
    IsIntegral.pow (IsIntegral.of_pow hm (by rw [hζm]; exact isIntegral_one)) _
  have hinv : ζ ^ (m - 1) * ζ = 1 := by rw [← pow_succ, Nat.sub_add_cancel hm, hζm]
  refine ⟨⟨ζ ^ (m - 1), hint⟩, 1, fun u => ⟨ζ • (f u).1, Submodule.smul_mem _ ζ (f u).2⟩, Λ', h, N', x₀, P', x,
    ?_, fun u => ?_, hs, hmem, hTp, hU', hTb', hTM', hN', hA, hP', fun u => ⟨(hx u).1, (hx u).2.1, hR _ _ (hx u).2.2⟩⟩
  · rw [Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 lam.isPrime.ne_top
  · show ((1 : ℕ) : T.Q.c.F) • ((f u).1 : T.R ((i : ℕ) + 1)) = (ζ ^ (m - 1)) • (ζ • ((f u).1 : T.R ((i : ℕ) + 1)))
    rw [Nat.cast_one, one_smul, smul_smul, hinv, one_smul]

end GlobalTheory.OrbitAdapt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrbitFamilyAdaptedLatticeSplitSupportStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem _root_.GlobalTheory.T.exists_orbit_family_adapted_lattice_split_support : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)) (U : Subgroup G) (lam : HeightOneSpectrum (𝓞 D.what₂.LL)) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)), IsOrbitFamily (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (badN D) (wtA (κ i)) (T.dδ ((i : ℕ) + 1) (κ i).n) (fun u : U => ℓ u) (fun u => ((f u).1 : T.R ((i : ℕ) + 1))) → ∃ (a : 𝓞 T.Q.c.F) (s : ℕ) (f' : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La), (s : 𝓞 D.what₂.LL) ∉ lam.asIdeal ∧ (∀ u, (s : T.Q.c.F) • ((f u).1 : T.R ((i : ℕ) + 1)) = (a : T.Q.c.F) • ((f' u).1 : T.R ((i : ℕ) + 1))) ∧ SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h ∧ (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) ∧ Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) ∧ Λ.Unimod ∧ Λ.TrivAt (badN D) ∧ Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧ Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧ AdmX (l := T.Q.l) true x₀ ∧ P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) ∧ ∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f' u).1 : T.R ((i : ℕ) + 1)) := by
  first | exact @GlobalTheory.OrbitAdapt.exists_adapted | exact GlobalTheory.OrbitAdapt.exists_adapted | (intros; apply GlobalTheory.OrbitAdapt.exists_adapted <;> assumption)
end
end
