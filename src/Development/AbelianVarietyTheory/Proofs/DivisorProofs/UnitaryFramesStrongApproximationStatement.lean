module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealUnitaryCovolumeSumStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrameStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeCongruenceSubgroupsStatement
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeRealCompletion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureUnitaryLatticeFamilyStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianGramDiagonalSignatureUnitary

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

noncomputable section
namespace GlobalTheory.SUCovolConj
open MeasureTheory Set
open scoped Pointwise

section General

variable {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

theorem isFundamentalDomain_conj (μ : Measure X) [μ.IsMulLeftInvariant] [SFinite μ]
    (H H' : Subgroup X) (s : X) (hH : ∀ g, g ∈ H' ↔ s⁻¹ * g * s ∈ H) {D : Set X}
    (hD : IsFundamentalDomain H D μ) :
    IsFundamentalDomain H' ((MulAut.conj s).toEquiv '' D) μ := by
  refine hD.image_of_equiv (MulAut.conj s).toEquiv ?_
    { toFun := fun g => ⟨s⁻¹ * g.1 * s, (hH g.1).1 g.2⟩
      invFun := fun g => ⟨s * g.1 * s⁻¹, (hH _).2 (by simpa [mul_assoc] using g.2)⟩
      left_inv := fun g => by ext; simp [mul_assoc]
      right_inv := fun g => by ext; simp [mul_assoc] } ?_
  · have : ((MulAut.conj s).toEquiv.symm : X → X) = (fun x => x * s) ∘ (fun x => s⁻¹ * x) := by
      funext x; simp [mul_assoc]
    rw [this]
    exact (quasiMeasurePreserving_mul_right μ s).comp
      (measurePreserving_mul_left μ s⁻¹).quasiMeasurePreserving
  · intro g x
    simp [Subgroup.smul_def, mul_assoc]

theorem covolume_conj (μ : Measure X) [μ.IsMulLeftInvariant] [SFinite μ]
    (H H' : Subgroup X) [Countable H] [Countable H'] (s : X)
    (hH : ∀ g, g ∈ H' ↔ s⁻¹ * g * s ∈ H) :
    covolume H' X μ = covolume H X μ := by
  have hH2 : ∀ g, g ∈ H ↔ s⁻¹⁻¹ * g * s⁻¹ ∈ H' := fun g => by rw [hH]; simp [mul_assoc]
  by_cases h : HasFundamentalDomain H X μ
  · obtain ⟨D, hD⟩ := h.ExistsIsFundamentalDomain
    have h1 := isFundamentalDomain_conj μ H H' s hH hD
    have h2 : IsFundamentalDomain H ((Equiv.mulRight s⁻¹) '' D) μ := by
      refine hD.image_of_equiv (Equiv.mulRight s⁻¹) ?_ (Equiv.refl _) ?_
      · have : ((Equiv.mulRight s⁻¹).symm : X → X) = fun x => x * s := by funext x; simp
        rw [this]; exact quasiMeasurePreserving_mul_right μ s
      · intro g x; simp [Subgroup.smul_def, mul_assoc]
    rw [h1.covolume_eq_volume, hD.covolume_eq_volume, hD.measure_eq h2]
    have : (MulAut.conj s).toEquiv '' D = s • ((Equiv.mulRight s⁻¹) '' D) := by
      rw [← Set.image_smul, Set.image_image]
      refine Set.image_congr fun y _ => ?_
      simp [mul_assoc]
    rw [this, measure_smul]
  · have h' : ¬ HasFundamentalDomain H' X μ := by
      rintro ⟨D, hD⟩; exact h ⟨_, isFundamentalDomain_conj μ H' H s⁻¹ hH2 hD⟩
    simp [covolume, h, h']

end General
section Concrete

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gram_eq_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem det_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    (gram τ G M).det = M.det * (G.map τ).det * starRingEnd ℂ M.det := by
  rw [gram_eq_mul, det_mul, det_mul, det_transpose, (starRingEnd ℂ).map_det M, RingHom.mapMatrix_apply]

theorem col_eq_mulVec (M : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.col M a = M *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col (1 : Matrix (Fin r) (Fin r) ℂ) a := by
  ext k; simp [ReciprocityTheory.ChartRestriction.G.FD.col, mulVec, dotProduct, Matrix.one_apply]

theorem hermC_map_of_herm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E)
    (h2 : ∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) (u w : Fin r → ℂ) :
    hermC τ G (γ.map τ *ᵥ u) (γ.map τ *ᵥ w) = hermC τ G u w := by
  have key (a b : Fin r) : ∑ c, ∑ d, τ (γ c a) * τ (G c d) * (starRingEnd ℂ) (τ (γ d b)) =
      τ (G a b) := by
    have h := congrArg τ (h2 (Pi.single a 1) (Pi.single b 1))

    simp only [herm, cc, mulVec_single_one, Matrix.col_apply, map_sum, map_mul,
    IsCMField.complexEmbedding_complexConj] at h
    rw [h, Finset.sum_eq_single a (by intro c _ hc; simp [hc]) (by simp),
      Finset.sum_eq_single b (by intro c _ hc; simp [hc]) (by simp)]
    simp
  have hR : hermC τ G u w = ∑ a, ∑ b, u a *
      (∑ c, ∑ d, τ (γ c a) * τ (G c d) * (starRingEnd ℂ) (τ (γ d b))) * (starRingEnd ℂ) (w b) := by
    simp only [hermC, key]
  rw [hR]

  simp only [hermC, mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum,
  Finset.sum_mul]
  calc _ = ∑ c, ∑ d, ∑ a, ∑ b,
        u a * (τ (γ c a) * τ (G c d) * (starRingEnd ℂ) (τ (γ d b))) * (starRingEnd ℂ) (w b) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ = _ := by
        refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
        refine Finset.sum_congr rfl fun a _ => ?_
        exact (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans Finset.sum_comm

theorem hermC_smul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ) (u w : Fin r → ℂ) :
    hermC τ G (c • u) (c • w) = c * starRingEnd ℂ c * hermC τ G u w := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem countable_inReal (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (Γ : Subgroup (GL (Fin r) E)) : Countable (inReal Ψ G Γ) := by
  haveI : Countable E :=
    Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  haveI : Countable (GL (Fin r) E) :=
    Function.Injective.countable (f := (Units.val : GL (Fin r) E → _)) fun _ _ h => Units.ext h
  have : ((inReal Ψ G Γ : Subgroup (realSU Ψ G)) : Set (realSU Ψ G)).Countable := by
    refine ((Set.countable_range (embGL Ψ r)).preimage Subtype.val_injective).mono fun g hg => ?_
    obtain ⟨δ, -, hδ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hg)
    exact ⟨δ, hδ⟩
  exact this.to_subtype

end Concrete

theorem covolume_inReal_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (γ : GL (Fin r) E) (Δ : Subgroup (GL (Fin r) E)), (∀ a b, cc (G a b) = G b a) → (∀ τ : Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → (∀ u v, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) → covolume (inReal Ψ G (Δ.map (MulAut.conj γ).toMonoidHom)) (realSU Ψ G) (riemHaar Ψ G x) = covolume (inReal Ψ G Δ) (realSU Ψ G) (riemHaar Ψ G x) := by
  intro E _ _ _ r p0 Ψ G x γ Δ _hG hx hγ
  set A : Ψ → GL (Fin r) ℂ := embGL Ψ r γ with hAdef
  have hAv : ∀ τ : Ψ, ((A τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 := fun τ => rfl
  have hA : ∀ τ : Ψ, ∀ u w, hermC τ.1 G ((A τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ u)
      ((A τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ w) = hermC τ.1 G u w := by
    intro τ u w; rw [hAv]; exact hermC_map_of_herm τ.1 G _ hγ u w
  have hdet : ∀ τ : Ψ, (A τ : Matrix (Fin r) (Fin r) ℂ).det *
      starRingEnd ℂ (A τ : Matrix (Fin r) (Fin r) ℂ).det = 1 := by
    intro τ
    have hg : (G.map τ.1).det ≠ 0 := by
      intro h0
      have h1 := congrArg Matrix.det (hx τ)
      rw [det_gram, h0, mul_zero, zero_mul, det_diagonal] at h1
      refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
      simp only [sgn]; split_ifs <;> norm_num
    have e1 : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (A τ : Matrix (Fin r) (Fin r) ℂ) =
        ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G 1 := by
      ext a b
      simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply]
      rw [col_eq_mulVec (A τ : Matrix (Fin r) (Fin r) ℂ) a, col_eq_mulVec (A τ : Matrix (Fin r) (Fin r) ℂ) b, hA]
    have h2 := congrArg Matrix.det e1
    rw [det_gram, det_gram, det_one, map_one, one_mul, mul_one] at h2
    apply mul_right_cancel₀ hg
    linear_combination h2
  have hroot : ∀ τ : Ψ, ∃ m : ℂ, m ^ r = (A τ : Matrix (Fin r) (Fin r) ℂ).det ∧ m * starRingEnd ℂ m = 1 := by
    intro τ
    rcases Nat.eq_zero_or_pos r with hr | hr
    · refine ⟨1, ?_, by simp⟩
      subst hr; simp
    · obtain ⟨m, hm⟩ := IsAlgClosed.exists_pow_nat_eq ((A τ : Matrix (Fin r) (Fin r) ℂ).det) hr
      refine ⟨m, hm, ?_⟩
      have h1 : (m * starRingEnd ℂ m) ^ r = 1 := by rw [mul_pow, ← map_pow, hm, hdet τ]
      rw [Complex.mul_conj] at h1 ⊢
      have h3 : (Complex.normSq m) ^ r = 1 := by exact_mod_cast h1
      rw [(pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg m) hr.ne').1 h3]; simp
  choose m hm using hroot
  have hm0 : ∀ τ, m τ ≠ 0 := fun τ h => by simpa [h] using (hm τ).2
  let z : Ψ → GL (Fin r) ℂ := fun τ =>
    Units.map (algebraMap ℂ (Matrix (Fin r) (Fin r) ℂ)).toMonoidHom (Units.mk0 (m τ)⁻¹ (inv_ne_zero (hm0 τ)))
  have hzv : ∀ τ, ((z τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (m τ)⁻¹ • (1 : Matrix (Fin r) (Fin r) ℂ) := by
    intro τ; simp [z, Algebra.algebraMap_eq_smul_one]
  have hzc : ∀ g : Ψ → GL (Fin r) ℂ, z * g = g * z := by
    intro g; funext τ; ext1
    simp only [Pi.mul_apply, Units.val_mul, hzv, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  have hs0 : A * z ∈ realSU Ψ G := by
    intro τ
    have e : (((A * z) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        (m τ)⁻¹ • (A τ : Matrix (Fin r) (Fin r) ℂ) := by
      simp only [Pi.mul_apply, Units.val_mul, hzv, Matrix.mul_smul, mul_one]
    rw [e]
    refine ⟨?_, fun u w => ?_⟩
    · rw [det_smul, Fintype.card_fin, inv_pow, (hm τ).1]
      have : (A τ : Matrix (Fin r) (Fin r) ℂ).det ≠ 0 := fun h => by simpa [h] using hdet τ
      exact inv_mul_cancel₀ this
    · rw [Matrix.smul_mulVec, Matrix.smul_mulVec, hermC_smul, hA, map_inv₀, ← mul_inv,
        (hm τ).2, inv_one, one_mul]
  let s : realSU Ψ G := ⟨A * z, hs0⟩
  have hconj : ∀ g : Ψ → GL (Fin r) ℂ, (A * z)⁻¹ * g * (A * z) = A⁻¹ * g * A := by
    intro g
    calc (A * z)⁻¹ * g * (A * z) = z⁻¹ * (A⁻¹ * g * A) * z := by group
      _ = z⁻¹ * (z * (A⁻¹ * g * A)) := by rw [mul_assoc, ← hzc]
      _ = A⁻¹ * g * A := by group
  haveI := countable_inReal Ψ G Δ
  haveI := countable_inReal Ψ G (Δ.map (MulAut.conj γ).toMonoidHom)
  haveI : (riemHaar Ψ G x).IsMulLeftInvariant := by unfold riemHaar; infer_instance
  haveI : SFinite (riemHaar Ψ G x) := by unfold riemHaar tangentHaar; infer_instance
  have key : ∀ δ, embGL Ψ r ((MulAut.conj γ).toMonoidHom δ) = A * embGL Ψ r δ * A⁻¹ := by
    intro δ; simp [hAdef, MulAut.conj_apply, map_mul, map_inv]
  refine covolume_conj (riemHaar Ψ G x) _ _ s fun g => ?_
  simp only [inReal, Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hconj]
  constructor
  · rintro ⟨δ', ⟨δ, hδ, rfl⟩, h⟩
    refine ⟨δ, hδ, ?_⟩
    rw [← h, key]
    group
  · rintro ⟨δ, hδ, h⟩
    refine ⟨_, ⟨δ, hδ, rfl⟩, ?_⟩
    rw [key, h]
    group

end GlobalTheory.SUCovolConj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianGramDiagonalSignatureUnitaryStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal


theorem _root_.GlobalTheory.T.hermitian_gram_diagonal_signature_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (γ : GL (Fin r) E) (Δ : Subgroup (GL (Fin r) E)), (∀ a b, cc (G a b) = G b a) → (∀ τ : Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → (∀ u v, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) → covolume (inReal Ψ G (Δ.map (MulAut.conj γ).toMonoidHom)) (realSU Ψ G) (riemHaar Ψ G x) = covolume (inReal Ψ G Δ) (realSU Ψ G) (riemHaar Ψ G x) := by
  first | exact @GlobalTheory.SUCovolConj.covolume_inReal_conj | exact GlobalTheory.SUCovolConj.covolume_inReal_conj | (intros; apply GlobalTheory.SUCovolConj.covolume_inReal_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeRealCompletionStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal


theorem _root_.GlobalTheory.T.self_dual_lattice_real_completion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → ∃ L : Submodule (𝓞 E) (Fin r → E), (L : Set (Fin r → E)) = latOf (maximalRealSubfield E) g0 (Λ : Set (Fin r → E)) ∧ (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) = g0.mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) ∧ SelfDualLat G L := by
  first | exact @GlobalTheory.UCls.selfDual_latOf_translate | exact GlobalTheory.UCls.selfDual_latOf_translate | (intros; apply GlobalTheory.UCls.selfDual_latOf_translate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFramesStrongApproximation

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem GlobalTheory.ClassSum.sum_covolume_le : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M m : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (X : Fin m → Data E r) (g : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (x0 : ∀ i, Frame (X i).Ψ r) (S : Finset (Fin m)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), 2 ≤ r → 3 ≤ M → Unr E → SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → (∀ i, IsUA (IsCMField.complexConj E) G (g i)) → (∀ i ∈ S, TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M g0.det (g i).det) → (∀ i ∈ S, ∀ j ∈ S, UEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M (g i) (g j) → i = j) → (∀ i ∈ S, (X i).Gm = G ∧ (X i).Ψ = Ψ ∧ ((X i).Λ : Set (Fin r → E)) = latOf (maximalRealSubfield E) (g i) (Λ : Set (Fin r → E)) ∧ (∀ γ, γ ∈ (X i).Γ ↔ IsUStab G (X i).Λ γ ∧ ∀ x ∈ (X i).Λ, ∃ y ∈ (X i).Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) ∧ IsOrth (X i) (x0 i)) → ∑ i ∈ S, covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm) (riemHaar (X i).Ψ (X i).Gm (x0 i)) ≤ ENNReal.ofReal ((M : ℝ) ^ (2 * fdeg E * r ^ 2) * rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E) := by
  intro hP E _ _ _ r M m G Λ Ψ X g x0 S g0 hr hM hU hΛ hg0 hg hT hUE hX
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨i0, hi0⟩
  · subst hS; simp
  obtain ⟨hG0, hΨ0, -, -, hO0⟩ := hX i0 hi0
  subst hG0
  subst hΨ0
  obtain ⟨L, hLset, hLhat, hL⟩ := GlobalTheory.T.self_dual_lattice_real_completion E r (X i0).Gm Λ g0 hΛ hg0
  obtain ⟨γ, s, hγs, hpair⟩ := GlobalTheory.T.self_dual_lattice_congruence_subgroups E r M m (X i0).Gm Λ L g g0 S (fun i => (X i).Γ) (fun i => (X i).Λ)
    (by omega) hΛ hg0 hLset hLhat hg hT (fun i hi => ⟨(hX i hi).2.2.1, (hX i hi).2.2.2.1⟩)
  have hherm : ∀ a b, cc ((X i0).Gm a b) = (X i0).Gm b a := (X i0).Gm_herm
  have tr : ∀ (Ψ1 : Finset (E →+* ℂ)) (G1 : Matrix (Fin r) (Fin r) E) (x1 : Frame Ψ1 r) (p1 : ℕ)
      (H : Subgroup (GL (Fin r) E)), Ψ1 = (X i0).Ψ → G1 = (X i0).Gm →
      (∀ τ : Ψ1, gram τ.1 G1 (mat x1 τ) = Matrix.diagonal fun a : Fin r => ((sgn p1 (a : ℕ) : ℝ) : ℂ)) →
      covolume (inReal Ψ1 G1 H) (realSU Ψ1 G1) (riemHaar Ψ1 G1 x1) =
        covolume (inReal (X i0).Ψ (X i0).Gm H) (realSU (X i0).Ψ (X i0).Gm) (riemHaar (X i0).Ψ (X i0).Gm (x0 i0)) := by
    intro Ψ1 G1 x1 p1 H h1 h2 h3
    subst h1 h2
    rw [GlobalTheory.T.riemannianHaar_independent_of_orthonormal_frame E r p1 (X i0).p0 _ _ x1 (x0 i0) hherm h3 hO0]
  set Δ : Fin m → Subgroup (GL (Fin r) E) := fun i => ((X i).Γ).map (MulAut.conj (γ i)⁻¹).toMonoidHom with hΔ
  have hback : ∀ i, (Δ i).map (MulAut.conj (γ i)).toMonoidHom = (X i).Γ := by
    intro i
    rw [hΔ, Subgroup.map_map]
    have : (MulAut.conj (γ i)).toMonoidHom.comp (MulAut.conj (γ i)⁻¹).toMonoidHom = MonoidHom.id _ := by
      ext δ : 1
      simp [mul_assoc]
    rw [this, Subgroup.map_id]
  have hterm : ∀ i ∈ S, covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm)
      (riemHaar (X i).Ψ (X i).Gm (x0 i)) =
      covolume (inReal (X i0).Ψ (X i0).Gm (Δ i)) (realSU (X i0).Ψ (X i0).Gm) (riemHaar (X i0).Ψ (X i0).Gm (x0 i0)) := by
    intro i hi
    obtain ⟨hGi, hΨi, -, -, hOi⟩ := hX i hi
    rw [tr (X i).Ψ (X i).Gm (x0 i) (X i).p0 (X i).Γ hΨi hGi hOi, ← hback i]
    exact GlobalTheory.T.hermitian_gram_diagonal_signature_unitary E r (X i0).p0 (X i0).Ψ (X i0).Gm (x0 i0) (γ i) (Δ i) hherm hO0 (hγs i hi).1
  obtain ⟨J, t, ht, hcount⟩ := GlobalTheory.T.signature_unitary_lattice_family E r M (X i0).p0 (X i0).Gm L (X i0).Ψ (x0 i0) (Fin m) S s Δ hr
    (by omega) hL (X i0).cmType hO0 (fun i hi => (hγs i hi).2.1)
    (fun i hi j hj h => hUE i hi j hj (hpair i hi j hj h)) (fun i hi => (hγs i hi).2.2)
  have hV := GlobalTheory.T.real_unitary_covolume_sum hP E r (X i0) L (x0 i0) J t hr hU hL hO0 ht
  rw [Finset.sum_congr rfl hterm]
  refine hcount.trans ?_
  calc (M : ℝ≥0∞) ^ (2 * fdeg E * r ^ 2) * ∑' j, covolume (inReal (X i0).Ψ (X i0).Gm (ratStab (X i0).Gm (L : Set (Fin r → E)) (t j))) (realSU (X i0).Ψ (X i0).Gm) (riemHaar (X i0).Ψ (X i0).Gm (x0 i0))
      ≤ (M : ℝ≥0∞) ^ (2 * fdeg E * r ^ 2) * ENNReal.ofReal (rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E) := by
        gcongr
    _ = _ := by
        rw [mul_assoc ((M : ℝ) ^ (2 * fdeg E * r ^ 2)), ENNReal.ofReal_mul (p := (M : ℝ) ^ (2 * fdeg E * r ^ 2)) (by positivity),
          ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFramesStrongApproximationStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.unitary_frames_strong_approximation : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M m : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (X : Fin m → Data E r) (g : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (x0 : ∀ i, Frame (X i).Ψ r) (S : Finset (Fin m)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), 2 ≤ r → 3 ≤ M → Unr E → SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → (∀ i, IsUA (IsCMField.complexConj E) G (g i)) → (∀ i ∈ S, TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M g0.det (g i).det) → (∀ i ∈ S, ∀ j ∈ S, UEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M (g i) (g j) → i = j) → (∀ i ∈ S, (X i).Gm = G ∧ (X i).Ψ = Ψ ∧ ((X i).Λ : Set (Fin r → E)) = latOf (maximalRealSubfield E) (g i) (Λ : Set (Fin r → E)) ∧ (∀ γ, γ ∈ (X i).Γ ↔ IsUStab G (X i).Λ γ ∧ ∀ x ∈ (X i).Λ, ∃ y ∈ (X i).Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) ∧ IsOrth (X i) (x0 i)) → ∑ i ∈ S, covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm) (riemHaar (X i).Ψ (X i).Gm (x0 i)) ≤ ENNReal.ofReal ((M : ℝ) ^ (2 * fdeg E * r ^ 2) * rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E) := by
  first | exact @GlobalTheory.ClassSum.sum_covolume_le | exact GlobalTheory.ClassSum.sum_covolume_le | (intros; apply GlobalTheory.ClassSum.sum_covolume_le <;> assumption)
end
end
