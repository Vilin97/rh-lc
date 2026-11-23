module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharacterClosedFormStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizerStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymChainPatternIffPlaceConditionsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIteratedStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelCharacterByResidueCharacter
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZPosIxSuccInl

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.TopAgree

def zEquiv (κ l τ j : ℕ) : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin (κ + l + j * τ) :=
  (Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv

theorem zEquiv_val {κ l τ j : ℕ} (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) : (zEquiv κ l τ j a).val = zPos a := by
  rcases a with (i | i) | ⟨i, u⟩
  · simp [zEquiv, zPos]
  · simp [zEquiv, zPos]
  · simp [zEquiv, zPos]; ring

variable {E K : Type} [Field E] [NumberField E] [Field K] {P : HeightOneSpectrum (𝓞 E)}


open Classical in
def phiM (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ rS r t j N : ℕ)
    (M : ℕ → ℕ → E) : K :=
  if (∀ p p', p < N → p' < r + j * t → IntAt P (M p p')) ∧
      (∀ p p', r + j * t ≤ p → p < N → p' < r + j * t → IntAt P (M p p' / (q : E))) ∧
      (∀ p', p' < r → redP P (M p' p') = 1 ∧ ∀ p, p < r + j * t → p ≠ p' →
        (r ≤ p ∨ symIdx k₀ rS p' < symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) → redP P (M p p') = 0) ∧
      (∀ p p', r ≤ p' → p' < r + j * t → p < r + j * t → (p' - r) / t < (p - r) / t → redP P (M p p') = 0)
  then LocE.lamGvS ψ₀ χ k₀ r t j M *
    (LocE.unitV (χ j) (Matrix.det (Matrix.of fun s s' : Fin (r + j * t) => M s.1 s'.1)))⁻¹ else 0

theorem PhiGS_eq (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ rS r t j c' n' c n : ℕ) (x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) :
    LocE.PhiGS q ψ₀ χ k₀ rS r t (j + 1) c' n' c n x =
      phiM q ψ₀ χ k₀ rS r t j (n + c) (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x) := by
  rfl

variable {k : Type} [Field k]

theorem zPos_ixSucc_inl {κ l τ j : ℕ} (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) :
    zPos (ixSucc (Fin κ ⊕ Fin l) (Fin τ) j (Sum.inl a)) = zPos a := by
  rcases a with (i | i) | ⟨i, u⟩ <;> rfl

theorem zPos_ixSucc_inr {κ l τ j : ℕ} (u : Fin τ) :
    zPos (ixSucc (Fin κ ⊕ Fin l) (Fin τ) j (Sum.inr u)) = κ + l + j * τ + u := rfl

theorem zPos_lt {κ l τ j : ℕ} (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) : zPos a < κ + l + j * τ := by
  rw [← zEquiv_val]; exact (zEquiv κ l τ j a).isLt

theorem det_of_places (ι : E →+* k) {X : Type} [Fintype X] [DecidableEq X] {n : ℕ} (f : X ≃ Fin n) (pos : X → ℕ)
    (off : ℕ) (h : ∀ x, pos x = off + (f x).val) (M : ℕ → ℕ → E) :
    Matrix.det (Matrix.of fun x y => ι (M (pos x) (pos y))) =
      ι (Matrix.det (Matrix.of fun s s' : Fin n => M (off + s.1) (off + s'.1))) := by
  rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self f]
  congr 1
  ext x y
  simp [h]

end GlobalTheory.SymBridge.TopAgree
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLIffIsUnitDetAtPrime

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.SymBridge

theorem mem_KO_iff_intAt_isUnit_det : ∀ (E k : Type) [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (κ l τ j : ℕ) (M : ℕ → ℕ → E), (∃ g ∈ KO k (Ix (Fin κ ⊕ Fin l) (Fin τ) j), g.val = Matrix.of fun a b => ι (M (zPos a) (zPos b))) ↔ (∀ p p', p < κ + l + j * τ → p' < κ + l + j * τ → IntAt P (M p p')) ∧ IsUnit (redP P (Matrix.det (Matrix.of fun s s' : Fin (κ + l + j * τ) => M s.1 s'.1))) := by
  intro E k _ _ _ _ _ _ _ P q ι ϖ hC hU κ l τ j M
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι ϖ hC hU
  let e : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin (κ + l + j * τ) :=
    (Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv
  have he : ∀ a, ((e a : Fin _) : ℕ) = zPos a := by
    rintro ((i | i) | ⟨i, u⟩) <;> simp [e, zPos, finProdFinEquiv] <;> ring
  let A : Matrix (Fin (κ + l + j * τ)) (Fin (κ + l + j * τ)) E := Matrix.of fun s s' => M s.1 s'.1
  let T : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k :=
    Matrix.of fun a b => ι (M (zPos a) (zPos b))
  have hT : T = (A.map ι).submatrix e e := by
    ext a b; simp [T, A, he]
  have hdet : T.det = ι A.det := by
    rw [hT, Matrix.det_submatrix_equiv_self, RingHom.map_det]; rfl
  have hint : ∀ x : k, valuation k x = 1 → x ∈ 𝒪[k] := fun x hx =>
    (Valuation.mem_integer_iff (valuation k) x).2 hx.le
  change (∃ g ∈ KO k (Ix (Fin κ ⊕ Fin l) (Fin τ) j), g.val = T) ↔ _
  constructor
  · rintro ⟨g, hg, hgv⟩
    have hI := intM_of_mem_KO hg
    rw [hgv] at hI
    refine ⟨fun p p' hp hp' => ?_, ?_⟩
    · have h := hI (e.symm ⟨p, hp⟩) (e.symm ⟨p', hp'⟩)
      simp only [T, Matrix.of_apply] at h
      rw [← he, ← he, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact (hC.int _).1 h
    · have hv := valuation_det_of_mem_KO hg
      rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, hdet] at hv
      exact (h3 _ ((hC.int _).1 (hint _ hv))).1 hv
  · rintro ⟨hent, hunit⟩
    have hTint : ∀ a b, T a b ∈ 𝒪[k] := fun a b =>
      (hC.int _).2 (hent _ _ (he a ▸ (e a).2) (he b ▸ (e b).2))
    let B : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) 𝒪[k] :=
      Matrix.of fun a b => ⟨T a b, hTint a b⟩
    have hB : B.map (algebraMap 𝒪[k] k) = T := by ext a b; rfl
    have hBdet : algebraMap 𝒪[k] k B.det = ι A.det := by
      rw [RingHom.map_det]; change (B.map (algebraMap 𝒪[k] k)).det = _; rw [hB, hdet]
    have hAint : IntAt P A.det := (hC.int _).1 (hBdet ▸ (B.det).2)
    have hv : valuation k (ι A.det) = 1 := (h3 _ hAint).2 hunit
    have hBu : IsUnit B.det :=
      (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 (by rw [hBdet]; exact hv)
    refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (B.nonsingInvUnit hBu), ⟨_, rfl⟩, ?_⟩
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply]
    rfl

end GlobalTheory.SymBridge
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLIffIsUnitDetAtPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.mem_integralGL_iff_isUnit_det_at_prime : ∀ (E k : Type) [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (κ l τ j : ℕ) (M : ℕ → ℕ → E), (∃ g ∈ KO k (Ix (Fin κ ⊕ Fin l) (Fin τ) j), g.val = Matrix.of fun a b => ι (M (zPos a) (zPos b))) ↔ (∀ p p', p < κ + l + j * τ → p' < κ + l + j * τ → IntAt P (M p p')) ∧ IsUnit (redP P (Matrix.det (Matrix.of fun s s' : Fin (κ + l + j * τ) => M s.1 s'.1))) := by
  first | exact @GlobalTheory.SymBridge.mem_KO_iff_intAt_isUnit_det | exact GlobalTheory.SymBridge.mem_KO_iff_intAt_isUnit_det | (intros; apply GlobalTheory.SymBridge.mem_KO_iff_intAt_isUnit_det <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelCharacterAtRationalPoint

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem GlobalTheory.symLevel_lam_residue_elim : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (M : ℕ → ℕ → E), (∀ p p', p < κ + (s + 1) → p' < κ + (s + 1) → IntAt P (M p p')) → ∀ g : S.P.J, (g : GL (Fin κ ⊕ Fin (s + 1)) k).val = Matrix.of (fun a b => ι (M (Sum.elim (fun i => i.val) (fun i => κ + i.val) a) (Sum.elim (fun i => i.val) (fun i => κ + i.val) b))) → (S.P.lam g : ℂ) = σ₀ (ψ₀ (redP P (∑ i ∈ Finset.range (κ - 1), M i (i + 1) + ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1)))) := by
  intro E K k _ _ _ _ _ _ _ _ P q ι σ₀ ψ₀ χ s κ S hT M hM g hg
  exact GlobalTheory.symLevel_lam_residue E K k P q ι σ₀ ψ₀ χ s κ S hT M hM g hg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelCharacterAtRationalPointStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.symmetricLevel_character_at_rational_point : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (M : ℕ → ℕ → E), (∀ p p', p < κ + (s + 1) → p' < κ + (s + 1) → IntAt P (M p p')) → ∀ g : S.P.J, (g : GL (Fin κ ⊕ Fin (s + 1)) k).val = Matrix.of (fun a b => ι (M (Sum.elim (fun i => i.val) (fun i => κ + i.val) a) (Sum.elim (fun i => i.val) (fun i => κ + i.val) b))) → (S.P.lam g : ℂ) = σ₀ (ψ₀ (redP P (∑ i ∈ Finset.range (κ - 1), M i (i + 1) + ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1)))) := by
  first | exact @GlobalTheory.symLevel_lam_residue_elim | exact GlobalTheory.symLevel_lam_residue_elim | (intros; apply GlobalTheory.symLevel_lam_residue_elim <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepTestFunctionsAgreeRationalPoints

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.TopAgree
variable {E K k : Type} [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdOrd_top {κ τ s : ℕ} (b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 1)) :
    ∃ b', stdOrd (Fin κ) (Fin τ) (s + 1) 0 rfl b = Sum.inl b' ∧ xPos b' = zPos b := by
  rcases b with (i | i) | p
  · exact ⟨_, stdOrd_eps _ _ _ _ _ i, rfl⟩
  · have h := stdOrd_f (Fin κ) (Fin τ) (s + 1) 0 rfl i
    have e : (⟨0 + i.val, by omega⟩ : Fin (s + 1)) = i := Fin.ext (by simp)
    rw [e] at h
    exact ⟨_, h, rfl⟩
  · exact ⟨_, stdOrd_d _ _ _ _ _ p, rfl⟩

theorem top_entries (q : ℕ) (ι : E →+* k) {s κ : ℕ} (S : SymData k s κ) (τ n' n : ℕ)
    (e' : XIx (Fin κ) (Fin τ) (s + 1) ⊕ Fin 0 ≃ Fin (n' + 0)) (e : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ≃ Fin (n + 0))
    (he' : IsOrd (yPos xPos n') e') (he : IsOrd zPos e) (x : (Fin (n' + 0) → E) →ₗ[E] (Fin (n + 0) → E)) :
    (S.T (Fin τ)).PhiTop (toLoc ι e e' x) = S.P.iterPhi (Fin τ) S.μ S.tame (s + 1)
      (Matrix.of fun a b => ι (LocE.entB q κ 0 n' 0 n (fun i => i + 1) (fun i => i + 1) x (zPos a) (zPos b))) := by
  simp only [SymData.T, typeChain, Chain.ofType, LatFrame.transport, LatFrame.coords]
  congr 1
  have hb : (typeFrame S.ϖ (stdOrd (Fin κ) (Fin τ) (s + 1) 0 rfl)).bas.val = 1 := by
    ext (u | u) (v | v)
    · simp [typeFrame, embA, Matrix.one_apply]
    · exact v.elim0
    · exact u.elim0
    · exact u.elim0
  ext a b
  obtain ⟨b', hb1, hb2⟩ := stdOrd_top (κ := κ) (τ := τ) (s := s) b
  have ha : zPos a < n := by have := (e a).isLt; rw [he a] at this; omega
  have hb' : zPos b < n' := by
    have := (e' (Sum.inl b')).isLt; rw [he' (Sum.inl b')] at this; simp [yPos] at this; omega
  have h1 : ∀ p N, (if p < κ then p else if p < κ + 0 then N + (p - κ) else p - 0) = p := by
    intro p N; split_ifs <;> omega
  rw [hb]
  simp only [LatFrame.refl, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.submatrix_apply, id,
    Equiv.refl_apply, Matrix.of_apply, typeFrame, hb1, toLoc, LocE.entB, LocE.fIdx, LocE.scE, h1, if_pos ha, if_pos hb',
    sub_self, zpow_zero, mul_one, Loc.atN, dif_pos (show zPos a < n + 0 from ha)]
  have hv : (Pi.single (e' (Sum.inl b')) 1 : Fin (n' + 0) → E) = Loc.eN E (n' + 0) (zPos b) := by
    funext l
    simp only [Loc.eN, Pi.single_apply, Fin.ext_iff, he' (Sum.inl b'), yPos, Sum.elim_inl, hb2]
  rw [hv, show e a = ⟨zPos a, by omega⟩ from Fin.ext (he a)]

theorem bottom_iff {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {ϖ : kˣ} (hC : IsCompl P q ι ϖ)
    (hU : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (κ l τ j : ℕ) (M : ℕ → ℕ → E) :
    MaxM ((Matrix.of fun a b => ι (M (zPos a) (zPos b)) :
        Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) (j + 1)) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k).submatrix
          (ixSucc (Fin κ ⊕ Fin l) (Fin τ) j) id).toRows₂ ↔
      ∀ p p', κ + l + j * τ ≤ p → p < κ + l + (j + 1) * τ → p' < κ + l + j * τ → IntAt P (M p p' / (q : E)) := by
  have res := GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι ϖ hC hU
  constructor
  · intro h p p' hp hp' hp''
    have := h ⟨p - (κ + l + j * τ), by rw [Nat.add_mul] at hp'; omega⟩ ((zEquiv κ l τ j).symm ⟨p', hp''⟩)
    simp only [Matrix.toRows₂, Matrix.submatrix_apply, id, Matrix.of_apply, zPos_ixSucc_inr] at this
    rw [← zEquiv_val, Equiv.apply_symm_apply] at this
    rw [← (res.1 _)]
    convert this using 4
    omega
  · intro h u b
    simp only [Matrix.toRows₂, Matrix.submatrix_apply, id, Matrix.of_apply, zPos_ixSucc_inr]
    rw [res.1]
    exact h _ _ (by omega) (by rw [Nat.add_mul]; omega) (zPos_lt b)

theorem unit_char {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {σ₀ : K →+* ℂ} {ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K}
    {χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ} {s κ : ℕ} {S : SymData k s κ} (hT : Comparison₂ P q ι σ₀ ψ₀ χ S) (i : ℕ) (d : E) (u : kˣ)
    (hd : IntAt P d) (hu : valuation k (u : k) = 1) (e : (u : k) = ι d) :
    (S.μ (i + 1) u : ℂ) = σ₀ (LocE.unitV (χ i) d) := by
  have res := GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι S.ϖ hT.compl S.unif
  exact hT.chi i d u hd ((res.2.2.1 d hd).1 (e ▸ hu)) e

theorem intAt_div {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {a : E} (h : IntAt P (a / (q : E))) (hq : (q : E) ≠ 0) :
    IntAt P a := by
  have := h.mul (IntAt.coe P (q : 𝓞 E))
  simpa [div_mul_cancel₀ _ hq] using this

theorem core (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {s κ : ℕ} (S : SymData k s κ) (hT : Comparison₂ P q ι σ₀ ψ₀ χ S) (τ j N : ℕ)
    (hN : N = κ + s + 1 + (j + 1) * τ) (M : ℕ → ℕ → E) :
    S.P.iterPhi (Fin τ) S.μ S.tame j (Matrix.of fun a b => ι (M (zPos a) (zPos b))) =
      σ₀ (phiM q ψ₀ χ κ S.ρ (κ + s + 1) τ j N M) := by
  subst hN
  have hC := hT.compl
  have res := GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι S.ϖ hC S.unif
  have hq : (q : E) ≠ 0 := res.2.2.2.1
  have hpat := GlobalTheory.T.symmetricLevelChain_pattern_iterated k s κ S (Fin τ) j
  set T : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k :=
    Matrix.of fun a b => ι (M (zPos a) (zPos b)) with hTdef
  have hTop : ((Matrix.of fun a b => ι (M (zPos a) (zPos b)) :
      Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (j + 1)) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k).submatrix
        (ixSucc (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) id).toRows₁ = T := by
    ext a b; simp [Matrix.toRows₁, hTdef, zPos_ixSucc_inl]
  have hB := bottom_iff hC S.unif κ (s + 1) τ j M

  have hpatM := GlobalTheory.T.symChainPattern_iff_place_conditions E k P q ι S.ϖ hC S.unif κ (s + 1) S.ρ τ j M
  have hKO := GlobalTheory.T.mem_integralGL_iff_isUnit_det_at_prime E k P q ι S.ϖ hC S.unif κ (s + 1) τ j M
  simp only [TypeDatum.iterPhi, TypeDatum.Phi, hTop]
  unfold phiM
  by_cases hb : MaxM ((Matrix.of fun a b => ι (M (zPos a) (zPos b)) :
      Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (j + 1)) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k).submatrix
        (ixSucc (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) id).toRows₂
  swap
  · rw [if_neg hb, if_neg, map_zero]
    rintro ⟨-, h2, -⟩
    exact hb (hB.2 fun p p' h1 h1' h1'' => h2 p p' h1 (by rw [Nat.add_mul] at h1' ⊢; omega) h1'')
  rw [if_pos hb]
  have h2 := hB.1 hb
  have hzT : ∀ a b, T a b = ι (M (zPos a) (zPos b)) := fun a b => rfl
  have hdet : ∀ g : GL (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k, g.val = T →
      ((Matrix.GeneralLinearGroup.det g : kˣ) : k) =
        ι (Matrix.det (Matrix.of fun s' s'' : Fin (κ + s + 1 + j * τ) => M s'.1 s''.1)) := by
    intro g hg
    rw [Matrix.GeneralLinearGroup.val_det_apply, hg, hTdef,
      det_of_places ι (zEquiv κ (s + 1) τ j) zPos 0 (fun x => by simp [zEquiv_val]) M]
    simp only [zero_add]
    rfl
  have hintdet : ∀ g : GL (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k, g ∈ KO k _ → g.val = T →
      IntAt P (Matrix.det (Matrix.of fun s' s'' : Fin (κ + s + 1 + j * τ) => M s'.1 s''.1)) := by
    intro g hg hgT
    rw [← hC.int, ← hdet g hgT, Valuation.mem_integer_iff, valuation_det_of_mem_KO hg]
  by_cases hJ : ∃ g ∈ (S.P.iter (Fin τ) S.μ S.tame j).J, g.val = T
  · obtain ⟨g, hgJ, hgT⟩ := hJ
    obtain ⟨hgKO, hgpat⟩ := (hpat g).1 hgJ
    obtain ⟨hint, -⟩ := hKO.1 ⟨g, hgKO, hgT⟩
    have hpat' : ∀ (a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j),
        ¬FreeIx S.ρ a b → (valuation k) (ι (M (zPos a) (zPos b)) -
          (1 : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k) a b) < 1 := by
      intro a b hf; have := hgpat a b hf; rwa [hgT] at this
    obtain ⟨h3, h4⟩ := (hpatM hint).1 hpat'
    have hcond : (∀ p p', p < κ + s + 1 + (j + 1) * τ → p' < κ + s + 1 + j * τ → IntAt P (M p p')) ∧
        (∀ p p', κ + s + 1 + j * τ ≤ p → p < κ + s + 1 + (j + 1) * τ → p' < κ + s + 1 + j * τ →
          IntAt P (M p p' / (q : E))) ∧
        (∀ p', p' < κ + s + 1 → redP P (M p' p') = 1 ∧ ∀ p, p < κ + s + 1 + j * τ → p ≠ p' →
          (κ + s + 1 ≤ p ∨ symIdx κ S.ρ p' < symIdx κ S.ρ p ∨ (p' = κ + S.ρ ∧ p < κ)) → redP P (M p p') = 0) ∧
        (∀ p p', κ + s + 1 ≤ p' → p' < κ + s + 1 + j * τ → p < κ + s + 1 + j * τ →
          (p' - (κ + s + 1)) / τ < (p - (κ + s + 1)) / τ → redP P (M p p') = 0) := by
      refine ⟨fun p p' hp hp' => ?_, fun p p' hp hp' hp'' => h2 p p' hp hp' hp'', h3, h4⟩
      by_cases hpa : p < κ + s + 1 + j * τ
      · exact hint p p' hpa hp'
      · exact intAt_div (h2 p p' (by omega) hp hp') hq
    rw [if_pos hcond, ← hgT, extZ_coe _ _ ⟨g, hgJ⟩, TypeDatum.rho_apply]
    obtain ⟨g₀, D, hg₀, hD, hlam⟩ := GlobalTheory.T.iteratedDepthOneLevel_character_closed_form k _ (Fin τ) S.P S.μ S.tame j ⟨g, hgJ⟩
    rw [hlam]
    simp only [Units.val_mul, Units.coe_prod, Units.val_inv_eq_inv_val, LocE.lamGvS, map_mul, map_prod, map_inv₀]
    congr 2
    · refine GlobalTheory.T.symmetricLevel_character_at_rational_point E K k P q ι σ₀ ψ₀ χ s κ S hT M (fun p p' hp hp' => hint p p' (by omega) (by omega)) g₀ ?_
      rw [hg₀, hgT]
      ext (x | x) (y | y) <;> rfl
    · rw [← Fin.prod_univ_eq_prod_range]
      refine Finset.prod_congr rfl fun i _ => ?_
      have hdi : ((Matrix.GeneralLinearGroup.det (D i) : kˣ) : k) =
          ι (Matrix.det (Matrix.of fun u v : Fin τ =>
            M (κ + s + 1 + i.val * τ + u.val) (κ + s + 1 + i.val * τ + v.val))) := by
        rw [Matrix.GeneralLinearGroup.val_det_apply, (hD i).2, Ix.diagonalBlockOfMatrix, hgT]
        exact det_of_places ι (Equiv.refl _) (fun u : Fin τ => κ + s + 1 + i.val * τ + u.val) (κ + s + 1 + i.val * τ)
          (fun _ => rfl) M
      refine unit_char hT i _ _ ?_ (valuation_det_of_mem_KO (hD i).1) hdi
      rw [← hC.int, ← hdi, Valuation.mem_integer_iff, valuation_det_of_mem_KO (hD i).1]
    · exact unit_char hT j _ _ (hintdet g hgKO hgT) (valuation_det_of_mem_KO hgKO) (hdet g hgT)
  · rw [extZ_of_not _ _ hJ]
    split_ifs with hc
    · have hnu : ¬ IsUnit (redP P (Matrix.det (Matrix.of fun s' s'' : Fin (κ + s + 1 + j * τ) => M s'.1 s''.1))) := by
        intro hu
        have hint : ∀ p p', p < κ + (s + 1) + j * τ → p' < κ + (s + 1) + j * τ → IntAt P (M p p') :=
          fun p p' hp hp' => hc.1 p p' (by rw [Nat.add_mul]; omega) hp'
        obtain ⟨g, hgKO, hgT⟩ := hKO.2 ⟨hint, hu⟩
        refine hJ ⟨g, (hpat g).2 ⟨hgKO, fun a b hf => ?_⟩, hgT⟩
        rw [hgT]
        exact (hpatM hint).2 ⟨hc.2.2.1, hc.2.2.2⟩ a b hf
      rw [LocE.unitV, dite_eq_right hnu, _root_.inv_zero, mul_zero, map_zero]
    · rw [map_zero]

end GlobalTheory.SymBridge.TopAgree


open GlobalTheory.SymBridge.TopAgree in
theorem GlobalTheory.SymBridge.phiTopAgree_of_tie : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k)
    (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ),
    Comparison₂ P q ι σ₀ ψ₀ χ S → PhiTopAgree P q ι σ₀ ψ₀ χ S := by
  intro E K k _ _ _ _ _ _ _ _ P q ι σ₀ ψ₀ χ s κ S hT τ n' c' n hn' hc' hn e' e he' he x
  subst hc'
  rw [top_entries q ι S τ n' n e' e he' he x,
    core P q ι σ₀ ψ₀ χ S hT τ (s + 1) (n + 0) (by omega)]
  exact congrArg σ₀ (PhiGS_eq q ψ₀ χ κ S.ρ (κ + s + 1) τ (s + 1) 0 n' 0 n x).symm
end
end
end
