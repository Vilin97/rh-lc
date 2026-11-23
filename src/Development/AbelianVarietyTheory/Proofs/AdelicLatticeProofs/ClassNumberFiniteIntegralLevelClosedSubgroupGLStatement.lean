module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AdelicPairReducedBasisStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsQGroupWeilRestrictionStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteAdelicDoubleCosetsOfRationalSLSubgroupStatement
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Mathlib.CategoryTheory.Category.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GlFreeAlgebraToSpecialLinearEmbInjectiveHomStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GlFreeAlgebraEmbIntegralAndRational

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.EmbInt

theorem res_mul' {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) (g h : Matrix κ κ A) :
    res b (g * h) = res b g * res b h := by
  ext p q

  simp only [res, Matrix.of_apply, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply,
  Fintype.sum_prod_type]

theorem res_one' {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) :
    res b (1 : Matrix κ κ A) = 1 := by
  ext p q
  simp only [res, Matrix.of_apply, Matrix.one_apply]
  by_cases h : p.1 = q.1
  · rw [if_pos h, map_one, Matrix.one_apply]
    by_cases h' : p.2 = q.2
    · rw [if_pos h', if_pos (Prod.ext h h')]
    · rw [if_neg h', if_neg (fun e => h' (congrArg Prod.snd e))]
  · rw [if_neg h, map_zero, Matrix.zero_apply, if_neg (fun e => h (congrArg Prod.fst e))]

theorem repr_mem {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    (b : Module.Basis β R A) (R₀ : Subring R) (h1 : ∀ i, b.repr 1 i ∈ R₀) (x : A)
    (hx : ∀ p q, Algebra.leftMulMatrix b x p q ∈ R₀) (k : β) : b.repr x k ∈ R₀ := by

  have hsum : x = ∑ i, b.repr 1 i • (x * b i) := by
    conv_lhs => rw [← mul_one x, ← b.sum_repr 1]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _
  have hk : b.repr x k = ∑ i, b.repr 1 i * Algebra.leftMulMatrix b x k i := by
    conv_lhs => rw [hsum]

    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, Algebra.leftMulMatrix_eq_repr_mul]
  rw [hk]
  exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (h1 i) (hx k i)

theorem inv_mem {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (R₀ : Subring R)
    (M N : Matrix ι ι R) (hNM : N * M = 1) (hM : ∀ p q, M p q ∈ R₀) (hd : N.det ∈ R₀) (p q : ι) :
    N p q ∈ R₀ := by

  have hadj : N = N.det • M.adjugate := by
    have h1 : N * M * M.adjugate = M.adjugate := by rw [hNM, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h1
    have hd1 : N.det * M.det = 1 := by rw [← Matrix.det_mul, hNM, Matrix.det_one]
    rw [← h1, smul_smul, hd1, one_smul]

  let M' : Matrix ι ι R₀ := Matrix.of fun p q => ⟨M p q, hM p q⟩
  have hM' : R₀.subtype.mapMatrix M' = M := by ext; rfl
  have hA : M.adjugate p q = R₀.subtype (M'.adjugate p q) := by
    rw [← hM', ← RingHom.map_adjugate]; rfl
  rw [hadj, Matrix.smul_apply, smul_eq_mul, hA]
  exact Subring.mul_mem _ hd (M'.adjugate p q).2

theorem repr_map {F β : Type} [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F)
    {R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A]
    (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (x : F) (k : β) :
    b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k) := by

  have hq : ∀ c : ℚ, algebraMap R A (algebraMap ℚ R c) = algebraMap F A (algebraMap ℚ F c) := fun c =>
    DFunLike.congr_fun (RingHom.ext_rat ((algebraMap R A).comp (algebraMap ℚ R))
      ((algebraMap F A).comp (algebraMap ℚ F))) c
  have hx : algebraMap F A x = ∑ i, algebraMap ℚ R (ω.repr x i) • b i := by
    conv_lhs => rw [← ω.sum_repr x]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hq, hb]
  rw [hx, Module.Basis.repr_sum_self]

theorem res_map {F β : Type} [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F)
    {κ R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A]
    (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (g : Matrix κ κ F) :
    res b (g.map (algebraMap F A)) = (res ω g).map (algebraMap ℚ R) := by
  ext p q
  simp only [res, Matrix.of_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, hb,
    ← map_mul]
  exact repr_map ω b hb _ _

theorem emb_integral_and_rational : (∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) (R₀ : Subring R) (u : GL κ A), (∀ i, b.repr 1 i ∈ R₀) → (∀ p q, emb b u p q ∈ R₀) → ∀ i j k, b.repr ((u : Matrix κ κ A) i j) k ∈ R₀ ∧ b.repr (((u⁻¹ : GL κ A) : Matrix κ κ A) i j) k ∈ R₀) ∧ ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (κ : Type) [Fintype κ] [DecidableEq κ] (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ γ : GL κ F, emb b (Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ) = (emb ω γ).map (algebraMap ℚ R) := by
  refine ⟨fun R A β κ _ _ _ _ _ _ _ b R₀ u h1 he i j k => ?_,
    fun F β _ _ _ _ ω κ _ _ R A _ _ _ _ _ b hb γ => ?_⟩
  ·

    have hres : ∀ p q, res b (u : Matrix κ κ A) p q ∈ R₀ := fun p q => by
      simpa [emb] using he (Sum.inl p) (Sum.inl q)
    have hdet : (res b ((u⁻¹ : GL κ A) : Matrix κ κ A)).det ∈ R₀ := by
      simpa [emb] using he (Sum.inr ()) (Sum.inr ())
    have hinv : res b ((u⁻¹ : GL κ A) : Matrix κ κ A) * res b (u : Matrix κ κ A) = 1 := by
      rw [← res_mul', ← Units.val_mul, inv_mul_cancel, Units.val_one, res_one']
    have hres' : ∀ p q, res b ((u⁻¹ : GL κ A) : Matrix κ κ A) p q ∈ R₀ :=
      fun p q => inv_mem R₀ _ _ hinv hres hdet p q
    exact ⟨repr_mem b R₀ h1 _ (fun p q => hres (i, p) (j, q)) k,
      repr_mem b R₀ h1 _ (fun p q => hres' (i, p) (j, q)) k⟩
  · have hc : ((Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ : GL κ A) :
        Matrix κ κ A) = (γ : Matrix κ κ F).map (algebraMap F A) := rfl
    have hc' : (((Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ)⁻¹ : GL κ A) :
        Matrix κ κ A) = ((γ⁻¹ : GL κ F) : Matrix κ κ F).map (algebraMap F A) := by
      rw [← map_inv]; rfl
    unfold emb
    rw [hc, hc', res_map ω b hb, res_map ω b hb, Matrix.fromBlocks_map]
    ext (x | x) (y | y) <;> simp [RingHom.map_det]

end GlobalTheory.ClassFin.EmbInt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GlFreeAlgebraEmbIntegralAndRationalStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.glFreeAlgebraEmb_integral_and_rational : (∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) (R₀ : Subring R) (u : GL κ A), (∀ i, b.repr 1 i ∈ R₀) → (∀ p q, emb b u p q ∈ R₀) → ∀ i j k, b.repr ((u : Matrix κ κ A) i j) k ∈ R₀ ∧ b.repr (((u⁻¹ : GL κ A) : Matrix κ κ A) i j) k ∈ R₀) ∧ ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (κ : Type) [Fintype κ] [DecidableEq κ] (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ γ : GL κ F, emb b (Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ) = (emb ω γ).map (algebraMap ℚ R) := by
  first | exact @GlobalTheory.ClassFin.EmbInt.emb_integral_and_rational | exact GlobalTheory.ClassFin.EmbInt.emb_integral_and_rational | (intros; apply GlobalTheory.ClassFin.EmbInt.emb_integral_and_rational <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassNumberFiniteIntegralLevelClosedSubgroupGL

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.ClassFin

theorem classFinite_integralLevel : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ T : Finset (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), (∀ s ∈ T, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) ∧ ∀ x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) → ∃ γ : GL (Fin n) F, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((γ : GL (Fin n) (F)) : Matrix (Fin n) (Fin n) (F)) ij.1 ij.2) P = 0) ∧ ∃ s ∈ T, ∃ u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧ (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)) ∧ x = Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom γ * s * u := by
  intro F _ _ n S hS
  classical

  obtain ⟨R, _, _, R₀, _, b, hAP, hred, hb, hint⟩ :=
    GlobalTheory.T.adelic_pair_reduced_basis F _ (NumberField.RingOfIntegers.basis F)
  obtain ⟨Γ, hΓ, hcorr⟩ := GlobalTheory.T.exists_isQGroup_weilRestriction_alt F _ (NumberField.integralBasis F) n S hS
  have hbF : ∀ i, b i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (NumberField.integralBasis F i) := by
    intro i
    rw [hb i, NumberField.integralBasis_apply]
  have hA := hcorr R (FiniteAdeleRing (𝓞 F) F) b hbF
  have hQ := hcorr ℚ F (NumberField.integralBasis F) (fun i => rfl)
  obtain ⟨T₀, hT₀, hdec⟩ := GlobalTheory.T.finiteAdelicDoubleCosets_of_rational_SL_subgroup _ Γ R R₀ hΓ hAP

  let lift : Matrix ((Fin n × _) ⊕ Unit) ((Fin n × _) ⊕ Unit) R → GL (Fin n) (FiniteAdeleRing (𝓞 F) F) :=
    fun s => if h : ∃ g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F),
        (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n =>
          ((g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧
        s = GlobalTheory.ClassFin.emb b g then h.choose else 1
  have hlift : ∀ s ∈ pts Γ R, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n =>
      ((lift s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧
      s = GlobalTheory.ClassFin.emb b (lift s) := by
    intro s hs
    have h := hA.1 s hs
    simp only [lift, dif_pos h]
    exact h.choose_spec
  obtain ⟨hemb1, hembmul, -, hembinj⟩ := GlobalTheory.T.glFreeAlgebraToSpecialLinearEmb_injective_hom R (FiniteAdeleRing (𝓞 F) F) _ (Fin n) b
  refine ⟨T₀.image lift, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    exact (hlift s (hT₀ s hs)).1
  · intro x hx
    obtain ⟨γ₀, hγ₀, s, hs, u₀, hu₀, hu₀int, hx₀⟩ := hdec _ (hA.2 hred x hx)
    obtain ⟨γ, hγS, rfl⟩ := hQ.1 γ₀ hγ₀
    obtain ⟨u, huS, rfl⟩ := hA.1 u₀ hu₀
    obtain ⟨hsS, hsemb⟩ := hlift s (hT₀ s hs)
    have h1 : ∀ i, b.repr 1 i ∈ R₀ := by
      refine (hint 1).1 ?_
      intro v
      exact (HeightOneSpectrum.adicCompletionIntegers F v).one_mem
    have hunits := GlobalTheory.T.glFreeAlgebraEmb_integral_and_rational.1 R _ _ (Fin n) b R₀ u h1 hu₀int
    refine ⟨γ, hγS, lift s, Finset.mem_image_of_mem lift hs, u, huS, ?_, ?_⟩
    · intro i j
      exact ⟨(hint _).2 (fun k => (hunits i j k).1), (hint _).2 (fun k => (hunits i j k).2)⟩
    · apply hembinj
      simp only [hembmul]
      rw [hx₀, ← hsemb, GlobalTheory.T.glFreeAlgebraEmb_integral_and_rational.2 F _ (NumberField.integralBasis F) (Fin n) R _ b hbF γ]

end GlobalTheory.ClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassNumberFiniteIntegralLevelClosedSubgroupGLStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.classNumber_finite_integralLevel_closedSubgroupGL : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ T : Finset (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), (∀ s ∈ T, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) ∧ ∀ x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) → ∃ γ : GL (Fin n) F, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((γ : GL (Fin n) (F)) : Matrix (Fin n) (Fin n) (F)) ij.1 ij.2) P = 0) ∧ ∃ s ∈ T, ∃ u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧ (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)) ∧ x = Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom γ * s * u := by
  first | exact @GlobalTheory.ClassFin.classFinite_integralLevel | exact GlobalTheory.ClassFin.classFinite_integralLevel | (intros; apply GlobalTheory.ClassFin.classFinite_integralLevel <;> assumption)
end
end
