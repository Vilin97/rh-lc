module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocPAAAndPrimesNe
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantThird

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNormsUnit

theorem mem_of_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A} (h : P ∈ divs a) :
    a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · exact hf.mem_toFinset.1 h
  · simp at h

theorem qe_one {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} :
    QE sel ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
  have h : Qprime ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
    change Qprime (1 : Chr X.F X.E X.K) = ∅
    ext v
    simp [Qprime, MonoidHom.ker_one]
  unfold QE
  split_ifs with hf
  · rw [(Set.Finite.toFinset_eq_empty (h := hf)).2 h]
    rfl
  · rfl

theorem exists_prime {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {Sg : Set ℕ} (u : Pr.Word) (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∈ Sall sel (1 : Tup X.F X.E X.K Sg) u) :
    ∃ l : ℕ, l.Prime ∧ (l : 𝓞 X.E) ∈ P.asIdeal ∧ ¬ l ∣ Pr.cond := by
  classical
  have hg : ∀ i, P ∈ Pr.vG i → ∃ l : ℕ, l.Prime ∧ (l : 𝓞 X.E) ∈ P.asIdeal ∧ ¬ l ∣ Pr.cond := by
    intro i hi
    refine ⟨Pr.g i, hPr.g_prime i, hPr.piG_norm i ▸ P.asIdeal.mul_mem_left _ (mem_of_divs hi), fun hd => ?_⟩
    have h1 : Pr.g i ≡ 1 [MOD Pr.g i] := (hPr.g_cong i).of_dvd hd
    have h2 : Pr.g i ∣ 1 := (Nat.modEq_zero_iff_dvd).1 (h1.symm.trans ((Nat.modEq_zero_iff_dvd).2 dvd_rfl))
    exact (hPr.g_prime i).one_lt.ne' (Nat.dvd_one.1 h2)
  unfold Sall at hP
  simp only [rowSG, uSG, qe_one, Primes.vGs, Finset.mem_union, Finset.notMem_empty, or_false] at hP
  rcases hP with h | h | h
  · have h0 : Pr.piT u ∈ P.asIdeal := mem_of_divs h
    have hT : (Pr.T u : 𝓞 X.E) ∈ P.asIdeal := hPr.piT_norm u ▸ P.asIdeal.mul_mem_right _ h0
    refine ⟨Pr.T u, hPr.T_prime u, hT, fun hd => ?_⟩
    have h1 : (Pr.T u : 𝓞 X.E) ∣ Pr.piT u - 1 :=
      (Nat.cast_dvd_cast (hd.mul_right _)).trans (hPr.piT_cong u)
    have h2 : Pr.piT u - 1 ∈ P.asIdeal := Ideal.mem_of_dvd _ h1 hT
    have h3 := P.asIdeal.sub_mem h0 h2
    rw [sub_sub_cancel] at h3
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  · exact hg 0 h
  · exact hg 1 h

end GlobalTheory.ColNormsUnit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SharpUnitAtBadPrimes

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.AAUnitS

theorem aaUnit_bad_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ B : Base D D.host.ccK dl, (ambOf s B χ cD).AAUnit (Sall sel mu u) := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ h B P hP
  have hcond := h.1.pr_cond
  obtain ⟨⟨-, -, -, hcc, -, -, -, -, -, hPr, -⟩, -, -, -, hmu, -⟩ := h
  subst hmu
  obtain ⟨l, hl, hlP, hd⟩ := GlobalTheory.ColNormsUnit.exists_prime hPr sel u P hP
  rw [hcond] at hd
  refine GlobalTheory.AAUnitAway.locP_AA D X s _ dl B χ cD P l hl ?_ ?_ hlP ?_
  · intro hs
    exact hd (((Nat.dvd_of_mem_primeFactors hs).mul_right _).mul_right _)
  · rintro rfl
    exact hd ((dvd_mul_left _ _).mul_right _)
  · rw [hcc, Ideal.absNorm_top]
    exact Nat.coprime_one_left _

end GlobalTheory.Core.Ht2.AAUnitS
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SharpUnitAtBadPrimesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.periodLatticeIdeal_trivial_at_badPrimes : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ B : Base D D.host.ccK dl, (ambOf s B χ cD).AAUnit (Sall sel mu u) := by
  first | exact @GlobalTheory.Core.Ht2.AAUnitS.aaUnit_bad_sharp | exact GlobalTheory.Core.Ht2.AAUnitS.aaUnit_bad_sharp | (intros; apply GlobalTheory.Core.Ht2.AAUnitS.aaUnit_bad_sharp <;> assumption)
end
end
