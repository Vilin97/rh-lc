module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PaddedLastEntry
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MeanPeriodLogarithms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardMatrixStepIndicesLeExpStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardOrbitsLeExp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainKernelBoundAtEmbeddingAnyLevelPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstCoupledKernelFiniteDatumLevelSizeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastKernelFiniteDatumBoundedLevelSizeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BadPrimesSharp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedEntryTypePrimeSupportPeriodSizeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSixth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFrLifts
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NcardYbSetLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientGramPosSemidefAndNormAtPlaceStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoupledClassSumCauchySchwarzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetCConstMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqNormClassSumMatrixLeCauchySchwarzStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixEntryFiniteDatumBoundedLevelSize

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.EntryDatumS

open GlobalTheory.ColNorms.EntryDatum

theorem smallDatum_xiEntry_sharp : ∃ C : ℕ, ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 2 < N.R.m → ∀ (al : I.β i) (be : I.β (i + 1)) (p : ChPt (R := N.R) sel mu u i) (p' : ChPt (R := N.R) sel mu u (i + 1)), SmallDatum (Sall sel mu u) p.deco.1.N p'.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiEntry Ch sel mu cst I i al be p p') (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.unfoldedEntry_typePrime_support_period_size
  refine ⟨C, fun CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be p p' => ?_⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hg : ∀ i, Pr.g i = N.g i := H.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfr : ∀ {j : ℕ} (p : ChPt (R := N.R) sel mu u j) (P : rowSG Pr sel mu) x,
      frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (N.R.N j) P.1 := by
    intro j p P x
    have hP := h1 P.1 P.2
    unfold frsF
    rw [dite_eq_left hP]
    exact (GlobalTheory.ColNorms.liftFr_lifts X.E _ _ _ p.deco ⟨P.1, hP⟩).1 x
  have key := smallDatum_prod (K := X.K) (S := Sall sel mu u) p.deco.1 p'.deco.1 p'.deco.2 (frsF sel mu p) (frsF sel mu p')
    (hfr p) (hfr p') (fun P => by classical exact Finset.mem_union) (Pr.T u * (Pr.g 0 * Pr.g 1))
    (fun P hP => by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ (h3 P hP)) (fun P => Formalism.L2.Col.qOf P.1)
    (fun P => by
      obtain ⟨j, -, hj, -⟩ := h2 P.1 (h1 P.1 P.2)
      rw [hj]
      refine Dvd.dvd.mul_left ?_ _
      fin_cases j
      · exact Dvd.intro _ rfl
      · exact Dvd.intro_left _ rfl)
    (fun P => XiAt Ch sel mu cst i P (I.h i al P) (I.h (i + 1) be P)) _
    (hC CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be)
  have e : ∏ P : rowSG Pr sel mu, (Formalism.L2.Col.qOf P.1 : ℝ) ^ (C * N.R.m ^ 2 * N.Nm ^ 2) =
      ((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) := by
    rw [Finset.prod_pow, ← Nat.cast_prod, h4, hg 0, hg 1]
    push_cast
    rw [← pow_mul]
    congr 1
    ring
  rw [e] at key
  exact key

end GlobalTheory.Core.Ht2.EntryDatumS
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixEntryFiniteDatumBoundedLevelSizeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.matrix_entry_finite_datum_bounded_level_size : ∃ C : ℕ, ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 2 < N.R.m → ∀ (al : I.β i) (be : I.β (i + 1)) (p : ChPt (R := N.R) sel mu u i) (p' : ChPt (R := N.R) sel mu u (i + 1)), SmallDatum (Sall sel mu u) p.deco.1.N p'.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiEntry Ch sel mu cst I i al be p p') (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) := by
  first | exact @GlobalTheory.Core.Ht2.EntryDatumS.smallDatum_xiEntry_sharp | exact GlobalTheory.Core.Ht2.EntryDatumS.smallDatum_xiEntry_sharp | (intros; apply GlobalTheory.Core.Ht2.EntryDatumS.smallDatum_xiEntry_sharp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnNormsOf

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ColNorms

theorem errUnit_nonneg (N : NumDatum) {T : ℕ} (hT : 1 ≤ T) : 0 ≤ errUnit N T := by
  have h0 : (1 : ℝ) ≤ N.g 0 := by exact_mod_cast (N.g_prime 0).one_lt.le
  have h1 : (1 : ℝ) ≤ N.g 1 := by exact_mod_cast (N.g_prime 1).one_lt.le
  have h2 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have h3 : 0 ≤ Real.log ((N.g 0 : ℝ) * N.g 1 * T) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h0 h1) h2)
  unfold errUnit
  positivity

theorem kernelBound_ge (N : NumDatum) (δ : Code N) (T : ℕ) (C₁ C₂ : ℝ) (j : ℕ) (lo : RPl N.R → ℝ) (lt : ℝ) (h h' n n' : ℕ) :
    kernelBound_sq N δ T C₁ j lo lt 1 1 1 1 + 2 * (C₂ * errUnit N T) ≤ kernelBound_sq N δ T (C₁ + C₂) j lo lt h h' n n' := by
  have a1 : 0 ≤ Real.log ((h : ℝ) * h') := by exact_mod_cast Real.log_natCast_nonneg (h * h')
  have a2 : 0 ≤ Real.log ((n : ℝ) * n') := by exact_mod_cast Real.log_natCast_nonneg (n * n')
  unfold kernelBound_sq errUnit
  simp only [Nat.cast_one, mul_one, Real.log_one]
  nlinarith

theorem SmallDatum.mono {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}
    {S : Finset (HeightOneSpectrum (𝓞 E))} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {c : ℕ}
    {Ξ : HomE E a b → K} {β β' : ℝ} (h : SmallDatum S N N' c Ξ β) (hβ : β ≤ β') : SmallDatum S N N' c Ξ β' :=
  ⟨h.1, h.2.1, fun σ x => (h.2.2 σ x).trans hβ⟩

end GlobalTheory.ColNorms
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormsMatrixStepsCoupledFactorBoundedAnyLevelPrim

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Core.Ht2

theorem factors_leS : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound → FamilyTie → FamilyVectors → PeriodLattices → CosetRefinement → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod → ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (B : Base D D.host.ccK dl) (b : I.β (N.R.m - 2 + 1)) (hY : YbHyp (R := N.R) sel mu cst I u (N.R.m - 2) b) (hK : KerEquivC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch)) (hF : ∀ j, (chF W sel mu I u j).Ok) (hE : (evGSD W Ch sel mu (rPsymF Ch) u).Ok), FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hM : ThetaFieldData B cD s.σ₀ N.R M) (ρ : M →ₐ[ℚ] ℂ), (∀ i, i + 2 < N.R.m → StepBound_sq (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) i (placeUnder s.σ₀ hM.1 ρ) (liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ (i + 1))) ∧ CplBound_sq (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) (placeUnder s.σ₀ hM.1 ρ) (liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ (N.R.m - 1) + liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ N.R.m)  := by
  intro hB hT hV hL hR hP
  obtain ⟨Cd, hdat⟩ := GlobalTheory.T.matrix_entry_finite_datum_bounded_level_size
  obtain ⟨C₁, hC₁, hker⟩ := GlobalTheory.T.chainKernel_bound_at_embedding_anyLevelPrime hB hT hV hL hR hP Cd
  obtain ⟨Cc, hCc, hcl⟩ := GlobalTheory.ChainClassNumbersS.classNumbers_leS
  obtain ⟨Ci, hCi, hidx⟩ := GlobalTheory.T.card_matrixStep_indices_le_exp
  obtain ⟨Cy, hCy, hyb⟩ := GlobalTheory.CouplingCosetsS.ncard_ybSet_le
  refine ⟨C₁ + (Cc + Ci + Cy), by positivity, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B b hY hK hF hE hFD M _ hM ρ
  have hPr : Pr.Ok := H.1.2.2.2.2.2.2.2.2.2.1
  have hU := errUnit_nonneg N (hPr.T_prime u).one_lt.le
  have hm := N.R.two_le_m
  set U := errUnit N (Pr.T u) with hUdef
  set σ : X.K →+* ℂ := (ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1) with hσ
  set Q := KerChain.ofCol W Ch sel mu cst I
    (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE with hQ
  set kb : ℕ → ℝ := fun j => kernelBound_sq N δ (Pr.T u) C₁ j (fun z => logOmAt B cD M ρ (s.iT (pl z)))
    (logThAt B M ρ (N.R.N (j - 1)) (N.R.N j)) 1 1 1 1 with hkb
  have hlift : ∀ j, kb j + 2 * ((Cc + Ci + Cy) * U) ≤
      liftBound_sq N s W Ch sel mu cst I B cD pl u δ (C₁ + (Cc + Ci + Cy)) M ρ j := fun j =>
    kernelBound_ge N δ _ _ _ j _ _ _ _ _ _
  have hpos : ∀ {n : ℕ} (lam : X.Tau → DomWeight n),
      ((Matrix.of fun i j => pairVr X.emb lam 1 (bVV X.K lam i) (bVV X.K lam j)).map
        (placeUnder s.σ₀ hM.1 ρ).embedding).PosSemidef := fun lam => (GlobalTheory.T.coefficientGram_posSemidef_and_normAtPlace X.E X.K X.Tau X.emb _ lam _).1
  have hsq := fun {n : ℕ} (lam : X.Tau → DomWeight n) => (GlobalTheory.T.coefficientGram_posSemidef_and_normAtPlace X.E X.K X.Tau X.emb n lam σ).2
  have hk := hker CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B hFD
  obtain ⟨hc1, hc2, -⟩ := hcl CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hi1 := hidx CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hfam : ∀ j, ∀ φ : (Q.F j).Forms, 0 ≤ (famIpAt (Q.F j) (Q.hF j) (placeUnder s.σ₀ hM.1 ρ) φ φ).re := by
    intro j φ
    unfold famIpAt GSD.ipAt
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun b' _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun c _ => ?_
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    refine mul_nonneg (by positivity) ?_
    exact (sqAt_nonneg (W.lamTrue u j) σ _).trans_eq (hsq (W.lamTrue u j) _).symm
  have hone : (1 : ℝ) ≤ ((N.g 0 : ℝ) * N.g 1) ^ (Cd * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) := by
    have h0 : (1 : ℝ) ≤ N.g 0 := by exact_mod_cast (N.g_prime 0).one_lt.le
    have h1 : (1 : ℝ) ≤ N.g 1 := by exact_mod_cast (N.g_prime 1).one_lt.le
    exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le h0 h1)
  refine ⟨fun i hi φ => ?_, fun φ => ?_⟩
  · have h1 := GlobalTheory.T.sq_norm_classSumMatrix_le_cauchySchwarz X.K Q i (placeUnder s.σ₀ hM.1 ρ) (Real.exp (kb (i + 1))) (Real.exp (Cc * U)) (Real.exp (Cc * U))
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (fun _ => hpos (W.lamTrue u i))
      (fun _ => hpos (W.lamTrue u (i + 1))) (hc1 i (by omega)) (hc1 (i + 1) (by omega)) (by
        intro al be p p' x
        have h2 := hk i (i + 1) rfl (by omega) _ (frsF sel mu p) _ (frsF sel mu p') ⟨p.deco.2.lat, p.deco.2.uni⟩
          ⟨p'.deco.2.lat, p'.deco.2.uni⟩ _ (hdat CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be p p') M hM ρ x
        have e : (Q.kk i al be).k p p' = matK W Ch sel mu cst I (chTh W Ch sel mu cst (ambOf s B χ cD) u (N.R.m - 2)) i al be p p' := by
          exact congrArg (fun k : ClsKer _ _ => k.k p p') (dif_pos (show i < N.R.m - 2 by omega))
        rw [e]
        exact (hsq (W.lamTrue u (i + 1)) _).trans_le (h2.trans_eq (congrArg _ (hsq (W.lamTrue u i) _).symm))) φ
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (hfam i φ))
    have b1 : (Fintype.card (Q.F i).β : ℝ) ≤ Real.exp (Ci * U) := hi1 i (by omega)
    have b2 : (Fintype.card (Q.F (i + 1)).β : ℝ) ≤ Real.exp (Ci * U) := hi1 (i + 1) (by omega)
    calc _ ≤ Real.exp (Ci * U) * Real.exp (Ci * U) * Real.exp (Cc * U) * Real.exp (Cc * U) * Real.exp (kb (i + 1)) := by gcongr
      _ ≤ _ := by
        simp only [← Real.exp_add]
        refine Real.exp_le_exp.2 (le_trans ?_ (hlift _))
        nlinarith [mul_nonneg hCy hU]
  · have hNle : N.R.N (N.R.m - 2 + 1) ≤ N.Nm := by
      unfold NumDatum.Nm Ranks.N
      have : N.R.m - 2 + 1 ≤ N.R.m := by omega
      gcongr
    have h1 := GlobalTheory.T.coupled_class_sum_cauchy_schwarz X.K Q (placeUnder s.σ₀ hM.1 ρ) (Real.exp (kb (N.R.m - 2 + 1))) (Real.exp (kb N.R.m))
      (Real.exp (Cc * U)) (Real.exp (Cc * U)) (Real.exp (Cc * U)) (Real.exp (Cy * U))
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le
      (fun _ => hpos (W.lamTrue u (N.R.m - 2))) (hpos (W.lamTrue u (N.R.m - 2 + 1))) (hpos (W.lamTrue u N.R.m))
      (hc1 (N.R.m - 2) (by omega)) (hc1 (N.R.m - 2 + 1) (by omega) b) hc2
      (fun p => (hyb CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H _ hNle).2 _ p.deco.2.lat) (by
        intro al p₀ p Y hYm x
        have h2 := hk (N.R.m - 2) (N.R.m - 2 + 1) rfl (by omega) _ (frsF sel mu p₀) _ (frsF sel mu p)
          ⟨p₀.deco.2.lat, p₀.deco.2.uni⟩ ⟨p.deco.2.lat, p.deco.2.uni⟩ _
          ((GlobalTheory.T.firstCoupledKernel_finiteDatum_level_size CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H al p₀ p Y).mono hone) M hM ρ x
        have e : (Q.cp al).k1 p₀ p Y = kerOf (stepC W Ch sel mu cst (ambOf s B χ cD) u (N.R.m - 2) (W.lamTrue u (N.R.m - 2 + 1)))
            (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p₀.deco.1.N (frsF sel mu p₀) p.deco.1.N (frsF sel mu p)
            (XiCpl1 Ch sel mu cst I (N.R.m - 2) al p₀ p Y) := if_pos hYm
        rw [e]
        exact (hsq (W.lamTrue u (N.R.m - 2 + 1)) _).trans_le
          (h2.trans_eq (congrArg _ (hsq (W.lamTrue u (N.R.m - 2)) _).symm))) (by
        intro al p d Y hYm x
        have h2 := hk (N.R.m - 2 + 1) N.R.m (by omega) (by omega) _ (frsF sel mu p) _ (frsT sel mu u d)
          ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨(tilQ sel mu u d).2.lat, (tilQ sel mu u d).2.uni⟩ _
          ((GlobalTheory.T.lastKernelFiniteDatum_bounded_level_size CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H p d Y hYm).mono hone) M hM ρ x
        have e : (Q.cp al).k2 p Y d = kerOf (stepC W Ch sel mu cst (ambOf s B χ cD) u (N.R.m - 2 + 1) (W.lamTrue u N.R.m))
            (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p) (tilQ sel mu u d).1.N
            (frsT sel mu u d) (XiCpl2 Ch sel mu cst (N.R.m - 2) p Y d) := if_pos hYm
        rw [e]
        exact (hsq (W.lamTrue u N.R.m) _).trans_le
          (h2.trans_eq (congrArg _ (hsq (W.lamTrue u (N.R.m - 2 + 1)) _).symm))) φ
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (hfam _ φ))
    have b1 : (Fintype.card (Q.F Q.n).β : ℝ) ≤ Real.exp (Ci * U) := hi1 (N.R.m - 2) (by omega)
    have e1 : N.R.m - 2 + 1 = N.R.m - 1 := by omega
    calc _ ≤ Real.exp (Ci * U) * Real.exp (Cc * U) * Real.exp (Cc * U) ^ 2 * Real.exp (Cc * U) * Real.exp (Cy * U) ^ 2 *
          Real.exp (kb (N.R.m - 2 + 1)) * Real.exp (kb N.R.m) := by gcongr
      _ ≤ _ := by
        simp only [sq, ← Real.exp_add]
        refine Real.exp_le_exp.2 (le_trans ?_ (add_le_add (hlift _) (hlift _)))
        rw [e1]
        nlinarith [mul_nonneg hCy hU, mul_nonneg hCi hU]

end GlobalTheory.Core.Ht2
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormsMatrixStepsCoupledFactorBoundedAnyLevelPrimStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.norms_matrixSteps_coupledFactor_bounded_anyLevelPrime : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound → FamilyTie → FamilyVectors → PeriodLattices → CosetRefinement → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod → ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (B : Base D D.host.ccK dl) (b : I.β (N.R.m - 2 + 1)) (hY : YbHyp (R := N.R) sel mu cst I u (N.R.m - 2) b) (hK : KerEquivC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch)) (hF : ∀ j, (chF W sel mu I u j).Ok) (hE : (evGSD W Ch sel mu (rPsymF Ch) u).Ok), FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hM : ThetaFieldData B cD s.σ₀ N.R M) (ρ : M →ₐ[ℚ] ℂ), (∀ i, i + 2 < N.R.m → StepBound_sq (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) i (placeUnder s.σ₀ hM.1 ρ) (liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ (i + 1))) ∧ CplBound_sq (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) (placeUnder s.σ₀ hM.1 ρ) (liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ (N.R.m - 1) + liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ N.R.m)  := by
  first | exact @GlobalTheory.Core.Ht2.factors_leS | exact GlobalTheory.Core.Ht2.factors_leS | (intros; apply GlobalTheory.Core.Ht2.factors_leS <;> assumption)
end
end
