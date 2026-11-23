module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfComps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvFinSSOneNot
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionArtinianRing
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenMulEqIdem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameCompletes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Mathlib.Tactic.TypeStar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemHROfGram

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WittS

section Abstract

variable {A B : Type} [CommRing A] [CommRing B]

theorem map_mul_of_mul (Q : B →+ A) (hQ : ∀ y y', Q (y * y') = Q y * Q y')
    {a b c : Type} [Fintype b] (X : Matrix a b B) (Y : Matrix b c B) :
    (X * Y).map Q = X.map Q * Y.map Q := by
  ext i j

  simp [Matrix.mul_apply, map_sum, hQ]

theorem exists_lift {m : Type} [Fintype m] [DecidableEq m] (c : A →+* A) (s : B →+* B) (P : A →+* B)
    (Q : B →+ A) (e : A) (hQs : ∀ y, Q (s y) = c (Q y)) (hQP : ∀ x, Q (P x) = e * x)
    (hQ : ∀ y y', Q (y * y') = Q y * Q y') (J : Matrix m m A) (g g' : Matrix m m B)
    (hgg' : g * g' = 1) (hg'g : g' * g = 1) (hU : (g.map s)ᵀ * J.map P * g = J.map P) :
    ∃ h h' : Matrix m m A, h * h' = 1 ∧ h' * h = 1 ∧ (h.map c)ᵀ * J * h = J ∧
      e • (h - 1) = h - 1 ∧
      ∀ (ι : Type) (N N' : Matrix m ι A), e • N = N → e • N' = N' → g * N.map P = N'.map P →
        h * N = N' := by
  have hQ1 : Q 1 = e := by simpa using hQP 1
  have hQe : ∀ y, e * Q y = Q y := fun y => by rw [← hQ1, ← hQ, one_mul]
  have hee : e * e = e := by simpa [hQ1] using hQe 1
  have hce : c e = e := by rw [← hQ1, ← hQs, map_one]
  have hGe : ∀ {a b : Type} (X : Matrix a b B), e • X.map Q = X.map Q := by
    intro a b X
    ext i j
    simp [hQe]
  have hfz : ∀ {a b : Type} (X : Matrix a b B), (1 - e) • X.map Q = 0 := by
    intro a b X
    rw [sub_smul, one_smul, hGe, sub_self]
  have h1Q : (1 : Matrix m m B).map Q = e • 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hQ1]
    · simp [Matrix.one_apply_ne hij]
  have hPQ : ∀ {a b : Type} (X : Matrix a b A), (X.map P).map Q = e • X := by
    intro a b X
    ext i j
    simp [hQP]
  have hfe : (1 - e) * (1 - e) = 1 - e := by linear_combination hee
  have hef : e * (1 - e) = 0 := by linear_combination -hee
  have hsum : ∀ {a b : Type} (X : Matrix a b A), e • X + (1 - e) • X = X := by
    intro a b X
    rw [← add_smul]
    simp
  have hmul : ∀ {a b c : Type} [Fintype b] (X : Matrix a b B) (Y : Matrix b c B),
      (X * Y).map Q = X.map Q * Y.map Q := fun X Y => map_mul_of_mul Q hQ X Y
  have hinv : ∀ u v : Matrix m m B, u * v = 1 →
      (u.map Q + (1 - e) • 1) * (v.map Q + (1 - e) • 1) = 1 := by
    intro u v huv
    rw [add_mul, mul_add, mul_add, ← hmul, huv, h1Q]
    simp only [smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hfz, smul_smul, hfe, add_zero,
      zero_add]
    exact hsum 1
  have hstar : ((g.map Q + (1 - e) • (1 : Matrix m m A)).map c)ᵀ =
      ((g.map s)ᵀ).map Q + (1 - e) • 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hQs, hce]
    · simp [hQs, hce, Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  refine ⟨g.map Q + (1 - e) • 1, g'.map Q + (1 - e) • 1, hinv _ _ hgg', hinv _ _ hg'g, ?_, ?_, ?_⟩
  · rw [hstar]
    have hJ : ((g.map s)ᵀ).map Q * J * g.map Q = e • J := by
      have h0 : ((g.map s)ᵀ).map Q * (e • J) = ((g.map s)ᵀ).map Q * J := by
        rw [mul_smul_comm, ← smul_mul_assoc, hGe]
      rw [← h0, ← hPQ J, ← hmul, ← hmul, hU]
    have hL : (1 - e) • (((g.map s)ᵀ).map Q * J) = 0 := by
      rw [← smul_mul_assoc, hfz, zero_mul]
    have hR : (1 - e) • (J * g.map Q) = 0 := by
      rw [← mul_smul_comm, hfz, mul_zero]
    simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hJ, hL, hR,
      smul_smul, hfe, add_zero, zero_add]
    exact hsum J
  · have h1 : g.map Q + (1 - e) • (1 : Matrix m m A) - 1 = g.map Q - e • 1 := by
      rw [sub_smul, one_smul]
      abel
    rw [h1, smul_sub, hGe, smul_smul, hee]
  · intro ι N N' hN hN' hg
    have hz : (1 - e) • N = 0 := by
      rw [sub_smul, one_smul, hN, sub_self]
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hz, add_zero]
    have h2 : g.map Q * N = g.map Q * (e • N) := by rw [hN]
    rw [h2, ← hPQ N, ← hmul, hg, hPQ, hN']

end Abstract

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_mem_HR_of_gram (σ : E →ₐ[F] E) (hCM : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J)
    (Ad : Type) [CommRing Ad] [Algebra F Ad] (R : Type) [CommRing R] [Algebra F R]
    [IsArtinianRing R] [IsReduced R] (e : Ad ⊗[F] E)
    (P : Ad ⊗[F] E →+* R ⊗[F] E) (Q : R ⊗[F] E →+ Ad ⊗[F] E)
    (hPinc : ∀ x, P (inclR Ad x) = inclR R x)
    (hPc : ∀ x, P (sigR Ad σ x) = sigR R σ (P x))
    (hQs : ∀ y, Q (sigR R σ y) = sigR Ad σ (Q y)) (hPQ : ∀ y, P (Q y) = y)
    (hQP : ∀ x, Q (P x) = e * x) (hQm : ∀ y y', Q (y * y') = Q y * Q y')
    (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι E) (hΓ : Γ.det ≠ 0)
    (N N' : Matrix (Fin M) ι (Ad ⊗[F] E)) (hN : e • N = N) (hN' : e • N' = N')
    (hG : (HMul.hMul (N.map (sigR Ad σ))ᵀ (HMul.hMul (J.map (inclR Ad) : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N : Matrix (Fin M) ι (Ad ⊗[F] E)) : Matrix ι ι (Ad ⊗[F] E)) = e • Γ.map (inclR Ad))
    (hG' : (HMul.hMul (N'.map (sigR Ad σ))ᵀ (HMul.hMul (J.map (inclR Ad) : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N' : Matrix (Fin M) ι (Ad ⊗[F] E)) : Matrix ι ι (Ad ⊗[F] E)) = e • Γ.map (inclR Ad)) :
    ∃ h : HR Ad σ J, e • ((h.1 : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) - 1) =
        (h.1 : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) - 1 ∧
      (HMul.hMul (h.1 : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N : Matrix (Fin M) ι (Ad ⊗[F] E)) = N' := by
  have hQ1 : Q 1 = e := by simpa using hQP 1
  have hPe : P e = 1 := by rw [← hQ1, hPQ]
  let eqv := Fintype.equivFin ι
  have gramX : ∀ N₀ : Matrix (Fin M) ι (Ad ⊗[F] E),
      (HMul.hMul (N₀.map (sigR Ad σ))ᵀ (HMul.hMul (J.map (inclR Ad) : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N₀ : Matrix (Fin M) ι (Ad ⊗[F] E)) : Matrix ι ι (Ad ⊗[F] E)) = e • Γ.map (inclR Ad) →
      gramR R σ J (fun a i => P (N₀ i (eqv.symm a))) =
        (Γ.submatrix eqv.symm eqv.symm).map (inclR R) := by
    intro N₀ h₀
    ext a b
    have h := congrArg (fun X : Matrix ι ι (Ad ⊗[F] E) => P (X (eqv.symm a) (eqv.symm b))) h₀

    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
    smul_eq_mul, map_sum, map_mul, hPc, hPe, one_mul, hPinc, Finset.mul_sum] at h
    simp only [gramR, hR, Formalism.UG.hform, JR, Matrix.map_apply, Matrix.submatrix_apply, mul_assoc]
    exact h
  have hXY := (gramX N hG).trans (gramX N' hG').symm
  have hdet : IsUnit (gramR R σ J (fun a i => P (N i (eqv.symm a)))).det := by
    rw [gramX N hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_submatrix_equiv_self]
    exact (isUnit_iff_ne_zero.mpr hΓ).map _
  obtain ⟨hU, hact⟩ := GlobalTheory.CompanionTheory.SW.WittTuples.exists_actW_eq_of_gramR_eq F E σ hCM M J hJ R _ _ _
    hXY hdet
  let g : GL (Fin M) (R ⊗[F] E) := HeckeCharacterZeroLocus.SiegelWeilU.HA.mat R σ J hU
  have hJP : (J.map (inclR Ad)).map P = J.map (inclR R) := by
    ext i j
    simp [hPinc]
  have hmem : ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map (sigR R σ))ᵀ *
      (J.map (inclR Ad)).map P * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (J.map (inclR Ad)).map P := by
    rw [hJP]
    let h' : HeckeCharacterZeroLocus.SiegelWeilU.HR R σ J := hU
    exact h'.2
  have hgN : (HMul.hMul (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (N.map P) : Matrix (Fin M) ι (R ⊗[F] E)) = N'.map P := by
    ext i k
    have := congrFun (congrFun hact (eqv k)) i
    simpa [GlobalTheory.CompanionTheory.SW.actW, HeckeCharacterZeroLocus.SiegelWeilU.actTup, Matrix.mulVec, dotProduct, Matrix.mul_apply, g]
      using this
  obtain ⟨h, h', h1, h2, h3, h4, h5⟩ := exists_lift (sigR Ad σ) (sigR R σ) P Q e hQs hQP hQm
    (J.map (inclR Ad)) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))
    ((g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (by simp) (by simp) hmem
  let u : GL (Fin M) (Ad ⊗[F] E) := ⟨h, h', h1, h2⟩
  have hu : u ∈ HR Ad σ J := h3
  exact ⟨⟨u, hu⟩, h4, h5 ι N N' hN hN' hgN⟩

end General

theorem exists_unitary_off_S : (∀ (D : D7) (S : Finset (Pl D)) (e : AE D), IsIdem S e → ∃ (R : Type) (_ : CommRing R) (_ : Algebra D.host.F R) (_ : IsArtinianRing R) (_ : IsReduced R) (P : AE D →+* R ⊗[D.host.F] D.host.E) (Q : R ⊗[D.host.F] D.host.E →+ AE D), (∀ x, P (incA D x) = inclR R x) ∧ (∀ x, P (cA D x) = sigR R D.sp.cm.sig (P x)) ∧ (∀ y, Q (sigR R D.sp.cm.sig y) = cA D (Q y)) ∧ (∀ y, P (Q y) = y) ∧ (∀ x, Q (P x) = e * x) ∧ ∀ y y', Q (y * y') = Q y * Q y') → ∀ (D : D7) (V : HSp D) (S : Finset (Pl D)) (e : AE D), IsIdem S e → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι D.host.E), Γ.det ≠ 0 → ∀ N N' : Matrix (Fin V.rank) ι (AE D), e • N = N → e • N' = N' → (HMul.hMul (N.map (cA D))ᵀ (HMul.hMul (gA V) N : Matrix (Fin V.rank) ι (AE D)) : Matrix ι ι (AE D)) = e • Γ.map (incA D) → (HMul.hMul (N'.map (cA D))ᵀ (HMul.hMul (gA V) N' : Matrix (Fin V.rank) ι (AE D)) : Matrix ι ι (AE D)) = e • Γ.map (incA D) → ∃ h : GA D V, e • (mt V h - 1) = mt V h - 1 ∧ (HMul.hMul (mt V h) N : Matrix (Fin V.rank) ι (AE D)) = N' := by
  intro H D V S e he ι _ _ Γ hΓ N N' hN hN' hG hG'
  obtain ⟨R, _, _, _, _, P, Q, hPinc, hPc, hQs, hPQ, hQP, hQm⟩ := H D S e he
  obtain ⟨h, h1, h2⟩ := exists_mem_HR_of_gram D.sp.cm.sig (isCMExt_host D) V.gram (isHermND_gram V)
    (AF D.host.F) R e P Q hPinc hPc hQs hPQ hQP hQm ι Γ hΓ N N' hN hN' hG hG'
  exact ⟨h, h1, h2⟩

end GlobalTheory.CompanionTheory.WittS
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFreeFramePairs

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FreeFrames

theorem isOpen_free_frame_pairs {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (r t a : ℕ) (e : R) (he : e * e = e) (U : Set R) (hU : IsOpen U) (h1 : (1 : R) ∈ U)
    (hb : ∀ x ∈ U, ∃ b, x * b = e) :
    IsOpen {z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R |
      ∃ (L₁ : Matrix (Fin r) (Fin a) R) (L₂ : Matrix (Fin t) (Fin a) R),
        L₁ * (e • z.1) = e • 1 ∧ L₁ * (e • z.2) = 0 ∧ L₂ * (e • z.1) = 0 ∧ L₂ * (e • z.2) = e • 1} := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro z₀ ⟨L₁, L₂, h11, h12, h21, h22⟩
  let L : Matrix (Fin r ⊕ Fin t) (Fin a) R := Matrix.fromRows L₁ L₂
  let Z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R → Matrix (Fin a) (Fin r ⊕ Fin t) R :=
    fun z => Matrix.fromCols (e • z.1) (e • z.2)
  let C : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R → Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R :=
    fun z => L * Z z + (1 - e) • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R)
  have hone : (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) = Matrix.fromBlocks 1 0 0 1 :=
    Matrix.fromBlocks_one.symm
  have hLZ : L * Z z₀ = e • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) := by
    simp only [L, Z]
    rw [Matrix.fromRows_mul_fromCols, h11, h12, h21, h22, hone, Matrix.fromBlocks_smul]
    simp only [smul_zero]
  have hC0 : C z₀ = 1 := by
    simp only [C]
    rw [hLZ, ← add_smul]
    simp
  have hZc : Continuous Z := by
    refine continuous_matrix fun i j => ?_
    cases j with
    | inl j =>
      have h : Continuous fun z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R => e * z.1 i j :=
        Continuous.mul continuous_const (continuous_fst.matrix_elem i j)
      simpa [Z] using h
    | inr j =>
      have h : Continuous fun z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R => e * z.2 i j :=
        Continuous.mul continuous_const (continuous_snd.matrix_elem i j)
      simpa [Z] using h
  have hCc : Continuous C := by
    exact (continuous_const.matrix_mul hZc).add continuous_const
  have hd : Continuous fun z => (C z).det := hCc.matrix_det
  have hnhds : (fun z => (C z).det) ⁻¹' U ∈ 𝓝 z₀ := by
    refine (hU.preimage hd).mem_nhds ?_
    simpa [Set.mem_preimage, hC0] using h1
  refine Filter.mem_of_superset hnhds ?_
  intro z hz
  obtain ⟨b, hb'⟩ := hb _ hz
  have hLz : L * Z z = C z - (1 - e) • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) := by
    simp only [C, add_sub_cancel_right]
  have hee : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have key : ((e * b) • ((C z).adjugate * L)) * Z z = e • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) := by
    rw [Matrix.smul_mul, Matrix.mul_assoc, hLz, Matrix.mul_sub, Matrix.adjugate_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_sub, smul_smul, smul_smul]
    have h2 : e * b * (1 - e) = 0 := by
      rw [mul_right_comm, hee, zero_mul]
    have h3 : e * b * (C z).det = e := by
      rw [mul_assoc, mul_comm b, hb', he]
    rw [h2, h3, zero_smul, sub_zero]
  set L' := (e * b) • ((C z).adjugate * L) with hL'
  have key' : Matrix.fromBlocks (L'.toRows₁ * (e • z.1)) (L'.toRows₁ * (e • z.2))
      (L'.toRows₂ * (e • z.1)) (L'.toRows₂ * (e • z.2)) =
      Matrix.fromBlocks (e • 1) 0 0 (e • 1) := by
    rw [← Matrix.fromRows_mul_fromCols, Matrix.fromRows_toRows]
    have := key
    simp only [Z] at this
    rw [this, hone, Matrix.fromBlocks_smul]
    simp only [smul_zero]
  obtain ⟨a1, a2, a3, a4⟩ := Matrix.fromBlocks_inj.1 key'
  exact ⟨L'.toRows₁, L'.toRows₂, a1, a2, a3, a4⟩

theorem isOpen_free : ∀ (D : D7) (r t a : ℕ) (e : AE D), e * e = e →
    (∃ U : Set (AE D), IsOpen U ∧ 1 ∈ U ∧ ∀ x ∈ U, ∃ b, x * b = e) →
    IsOpen {z : Mx D a r × Mx D a t | Free e (e • z.1, e • z.2)} := by
  rintro D r t a e he ⟨U, hU, h1, hb⟩
  exact isOpen_free_frame_pairs r t a e he U hU h1 hb

end GlobalTheory.CompanionTheory.FreeFrames
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdemExTrans

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RgTrans

private theorem mul_mul_mul_smul_eq_smul_mul_mul_mul {A : Type*} [CommRing A] {a b c d f : Type*} [Fintype b] [Fintype c]
    [Fintype d] (R : Matrix a b A) (P : Matrix b c A) (G : Matrix c d A) (X : Matrix d f A) (e : A) :
    R * (P * (G * (e • X))) = e • (R * (P * (G * X))) := by
  simp only [Matrix.mul_smul]

private theorem yv_smul_snd {D : D7} {r t : ℕ} (V : HSp D) (b₀ : HermE D r) (e : AE D)
    (w : Mx D V.rank r × Mx D V.rank t) :
    yv V b₀ (w.1, e • w.2) = e • yv V b₀ w :=
  mul_mul_mul_smul_eq_smul_mul_mul_mul _ _ _ _ e

theorem idemEx_trans : IdemEx → Trans := by
  intro hI D r t V b₀ hb₀ S e he
  have hee : e * e = e := ((hI D S).2 e he).1
  have hce : cA D e = e := ((hI D S).2 e he).2
  refine ⟨GlobalTheory.CompanionTheory.FreeFrames.isOpen_free D r t V.rank e hee
    (GlobalTheory.CompanionTheory.UnitNbhd.exists_open_mul_eq_idem GlobalTheory.CompanionTheory.AdeleComp.eq_zero_of_comps D S e he), ?_⟩
  intro z z' hz hz' hzc hz'c
  obtain ⟨Γ, hΓ, hN⟩ := GlobalTheory.CompanionTheory.FrameComplete.frame_completes D r t V b₀ hb₀ e hee hce
  obtain ⟨N, hNe, hNg, hN1, hN2⟩ := hN z hz hzc
  obtain ⟨N', hN'e, hN'g, hN'1, hN'2⟩ := hN z' hz' hz'c
  obtain ⟨h, hh, hhN⟩ := GlobalTheory.CompanionTheory.WittS.exists_unitary_off_S
    (GlobalTheory.CompanionTheory.SPartTensor.sPart GlobalTheory.CompanionTheory.AdeleComp.eq_zero_of_comps) D V S e he _ Γ hΓ N N'
    hNe hN'e hNg hN'g
  have hy : ∀ w : Mx D V.rank r × Mx D V.rank t, e • w.2 = w.2 → e • yv V b₀ w = yv V b₀ w := by
    intro w hw
    have key : yv V b₀ w = e • yv V b₀ w := by
      calc yv V b₀ w = yv V b₀ (w.1, e • w.2) := by rw [hw]
        _ = e • yv V b₀ w := yv_smul_snd V b₀ e w
    rw [key, smul_smul, hee]
  have h1 : mm (mt V h) z.1 = z'.1 := by
    ext i j
    rw [← hN'1, ← hhN]
    simp only [mm, Matrix.mul_apply, hN1]
  have h2 : mm (mt V h) (z.2 - mm z.1 (yv V b₀ z)) = z'.2 - mm z'.1 (yv V b₀ z') := by
    ext i j
    rw [← hN'2, ← hhN]
    simp only [mm, Matrix.mul_apply, hN2]
  refine ⟨h, yv V b₀ z' - yv V b₀ z, hh, ?_, ?_⟩
  · rw [smul_sub, hy z' hz'c.2.1, hy z hzc.2.1]
  · have h3 : mm (mt V h) (z.2 + mm z.1 (yv V b₀ z' - yv V b₀ z)) =
        mm (mt V h) (z.2 - mm z.1 (yv V b₀ z)) + mm (mm (mt V h) z.1) (yv V b₀ z') := by
      simp only [mm, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_assoc]
      abel
    refine Prod.ext h1.symm ?_
    rw [h3, h1, h2]
    simp only [mm, sub_add_cancel]

end GlobalTheory.CompanionTheory.RgTrans
end
end
