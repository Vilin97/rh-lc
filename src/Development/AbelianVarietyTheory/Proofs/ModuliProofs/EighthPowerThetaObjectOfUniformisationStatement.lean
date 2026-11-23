module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppellHumbertUniformisationRiemannFormStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
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
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueIsMonHomOfLinearMapLatticeAnyDimStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OLinearMatrixOfUnifPow
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ImInvIsHermitian
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoLinCombLamOfAppellHumbertStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalTorusAlgebraic
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OLinearMatrixOfUnifPow
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAVStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.exists_siegPre_iso_of_polAV : Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (K : Type) [Field K] (em : o →+* K) (h k : ℕ) (ζ : o) (ze : Kˣ) (P : Out.PolAV (Sp K)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp K)) ⟶ P.A)), P.g = h → (k : K) ≠ 0 → (ze : K) = em ζ → IsPrimitiveRoot ze k → (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ k = 1) → (∀ x y, Out.WeilIs P.A P.L k (lev x) (lev y) (unitOn (ze ^ omegaStd x y))) → ∃ (c : SiegPre h k ζ (spMap em)) (φ : c.A ≅ P.A), IsMonHom φ.hom ∧ c.Principal ∧ LBIso c.P ((abelian₂ P.A P.L).pull (lift (fst c.A c.A ≫ φ.hom) (snd c.A c.A ≫ φ.hom)).left) ∧ ∀ x, c.lev x ≫ φ.hom = lev x := by
  first | exact @GlobalTheory.exists_siegPre_of_polAV | exact GlobalTheory.exists_siegPre_of_polAV | (intros; apply GlobalTheory.exists_siegPre_of_polAV <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtOfLin

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SharpObj

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := (u.ker 0).mpr u.Λ.zero_mem

def exHom : Multiplicative (Fin g → ℂ) →* (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
  MonoidHom.mk' (fun z => u.ex z.toAdd) fun z w => u.ex_add _ _

theorem ex_zsmul (n : ℤ) (z : Fin g → ℂ) : u.ex (n • z) = u.ex z ^ n := by
  have h := map_zpow (exHom u) (Multiplicative.ofAdd z) n
  rw [← ofAdd_zsmul] at h
  simpa [exHom] using h

theorem ex_nsmul (n : ℕ) (z : Fin g → ℂ) : u.ex (n • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact ex_zero u
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem ex_sum [IsCommMonObj A] {I : Type} [Fintype I] (z : I → Fin g → ℂ) : u.ex (∑ i, z i) = ∏ i, u.ex (z i) := by
  classical
  have key : ∀ s : Finset I, u.ex (∑ i ∈ s, z i) = ∏ i ∈ s, u.ex (z i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact ex_zero u
    | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, u.ex_add, ih]
  exact key Finset.univ

end Unif

variable (laws : Out.Laws) (laws2 : Out.Laws2)
  (hc : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
  (hT : ThetaUnifAV)
include laws laws2 hc hT

theorem hom_ext_of_lin (P P' : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (u' : HolUnif P'.A P'.L P'.g)
    (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)) (f f' : P.A ⟶ P'.A) (hf : ∀ z, u'.ex (F z) = u.ex z ≫ f)
    (hf' : ∀ z, u'.ex (F z) = u.ex z ≫ f') (h1 : IsMonHom f) : f = f' := by
  have e : ∀ B : Over (Sp ℂ), ∀ [GrpObj B], (η[B] : 𝟙_ _ ⟶ B) = 1 := fun B _ => by rw [Hom.one_def]; simp
  have h2 : IsMonHom f' := laws.rigidity _ _ _ P.isAb P'.isAb f' (by
    rw [e, e, ← ex_zero u, ← hf', map_zero, ex_zero])
  refine (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim laws laws2 hc hT P P' _ _ u u' F fun z hz => ?_).unique ⟨h1, hf⟩ ⟨h2, hf'⟩
  rw [← u'.ker, hf, (u.ker z).2 hz, MonObj.one_comp]

theorem exists_proj (P P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (u₀ : HolUnif P₀.A P₀.L P₀.g)
    {I : Type} [Fintype I] (σ : I × Fin P₀.g ≃ Fin P.g)
    (hΛ : ∀ z, z ∈ u.Λ ↔ ∀ i, (fun j => z (σ (i, j))) ∈ u₀.Λ) :
    ∃ pr : I → (P.A ⟶ P₀.A), (∀ i, IsMonHom (pr i)) ∧ (∀ i z, u₀.ex (fun j => z (σ (i, j))) = u.ex z ≫ pr i) ∧
      ∀ (T : Over (Sp ℂ)) (y : I → (T ⟶ P₀.A)), ∃! x : T ⟶ P.A, ∀ i, x ≫ pr i = y i := by
  classical
  letI := P.isAb.comm
  letI := P₀.isAb.comm
  let R : I → (Fin P.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ) := fun i => LinearMap.funLeft ℂ ℂ fun j => σ (i, j)
  let S : I → (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ) := fun i =>
    LinearMap.pi fun a => if (σ.symm a).1 = i then LinearMap.proj (σ.symm a).2 else 0
  have hRS : ∀ i i' z, R i (S i' z) = if i = i' then z else 0 := fun i i' z => by
    ext j
    by_cases e : i = i' <;> simp [R, S, LinearMap.funLeft_apply, e]
  have hSR : ∀ z, ∑ i, S i (R i z) = z := fun z => by
    ext a
    obtain ⟨⟨i, j⟩, rfl⟩ := σ.surjective a
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp [R, S, LinearMap.funLeft_apply]
    · intro b _ hb
      simp [S, hb.symm]
    · simp
  choose pr hpr using fun i => (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim laws laws2 hc hT P P₀ _ _ u u₀ (R i) fun z hz => (hΛ z).1 hz i).exists
  choose inc hinc using fun i => (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim laws laws2 hc hT P₀ P _ _ u₀ u (S i) fun z hz => (hΛ _).2 fun i' => by
    change R i' (S i z) ∈ _
    rw [hRS]
    split_ifs
    exacts [hz, u₀.Λ.zero_mem]).exists
  haveI := fun i => (hpr i).1
  haveI := fun i => (hinc i).1
  have e1 : ∀ i, inc i ≫ pr i = 𝟙 _ := fun i =>
    hom_ext_of_lin laws laws2 hc hT P₀ P₀ u₀ u₀ LinearMap.id _ _ (fun z => by
      rw [← Category.assoc, ← (hinc i).2, ← (hpr i).2, hRS]; simp) (fun z => by simp) inferInstance
  have e2 : ∀ i i', i ≠ i' → inc i ≫ pr i' = 1 := fun i i' hi =>
    hom_ext_of_lin laws laws2 hc hT P₀ P₀ u₀ u₀ 0 _ _ (fun z => by
      rw [← Category.assoc, ← (hinc i).2, ← (hpr i').2, hRS]; simp [hi.symm])
      (fun z => by simp [ex_zero]) inferInstance
  have e3 : 𝟙 P.A = ∏ i, pr i ≫ inc i :=
    hom_ext_of_lin laws laws2 hc hT P P u u LinearMap.id _ _ (fun z => by simp) (fun z => by
      rw [PowMatrixLinear.comp_prod]
      simp only [← Category.assoc, ← (hpr _).2, ← (hinc _).2]
      rw [← ex_sum, hSR]; rfl) inferInstance
  refine ⟨pr, fun i => (hpr i).1, fun i => (hpr i).2, fun T y => ⟨∏ i, y i ≫ inc i, fun i => ?_, fun x hx => ?_⟩⟩
  · rw [PowMatrixLinear.prod_comp, Finset.prod_eq_single i]
    · rw [Category.assoc, e1, Category.comp_id]
    · intro b _ hb
      rw [Category.assoc, e2 _ _ hb, MonObj.comp_one]
    · simp
  · rw [← Category.comp_id x, e3, PowMatrixLinear.comp_prod]
    simp only [← Category.assoc, hx]

end GlobalTheory.SharpObj

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerThetaObjectOfUniformisation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

namespace SharpObj

theorem omegaStd_sum_smul {h : ℕ} {I : Type} [Fintype I] (x : Fin h ⊕ Fin h → ℤ) (c : I → ℤ)
    (y : I → Fin h ⊕ Fin h → ℤ) : omegaStd x (∑ v, c v • y v) = ∑ v, c v * omegaStd x (y v) := by
  simp only [omegaStd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem form_act {h : ℕ} (G A : Matrix (Fin 8) (Fin 8) ℤ) (x : Fin 8 → Fin h ⊕ Fin h → ℤ) :
    ∑ u, ∑ v, G u v * omegaStd (x u) (∑ v', A v v' • x v') = ∑ u, ∑ v, (G * A) u v * omegaStd (x u) (x v) := by
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [omegaStd_sum_smul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
  exact Finset.sum_comm

theorem exp_pi_I_int (n : ℤ) : Complex.exp (Real.pi * Complex.I * (n : ℂ)) = (-1) ^ n := by
  rw [_root_.mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem hermForm_eq_sum {g h : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (H₀ : Matrix (Fin h) (Fin h) ℂ)
    (G : Matrix (Fin 8) (Fin 8) ℤ) (R : Fin 8 → ((Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ))) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤)
    (h0 : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm z w).im = ∑ i, ∑ j, (G i j : ℝ) * (hermForm H₀ (R i z) (R j w)).im) (z w) :
    hermForm Hm z w = ∑ i, ∑ j, (G i j : ℂ) * hermForm H₀ (R i z) (R j w) := by
  refine sub_eq_zero.1 (form_ext s hs
    (fun z w => hermForm Hm z w - ∑ i, ∑ j, (G i j : ℂ) * hermForm H₀ (R i z) (R j w)) ?_ ?_ ?_ ?_ ?_ z w)
  · intro z z' w
    simp only [hermForm, map_add (f := _), add_dotProduct, mul_add, Finset.sum_add_distrib]
    ring
  · intro z w w'
    simp only [hermForm, map_add (f := _), star_add, Matrix.mulVec_add, dotProduct_add, mul_add, Finset.sum_add_distrib]
    ring
  · intro c z w
    simp only [hermForm, map_smul, smul_dotProduct, smul_eq_mul, mul_sub, Finset.mul_sum, mul_left_comm c]
  · intro c z w
    simp only [hermForm, map_smul, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_sub,
      Finset.mul_sum, Complex.star_def, Complex.conj_ofReal, mul_left_comm (c : ℂ)]
  · intro z hz w hw
    simp [h0 z hz w hw, Complex.im_sum]

end SharpObj


open SharpObj in
theorem sharpClass_of_unif : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (σ : Fin 8 × Fin h ≃ Fin g) (EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ x y, EF x y = ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (x u) (y v)) → ∀ (t : TObj g k J b (spMap em)) (τ : Matrix (Fin h) (Fin h) ℂ) (m : (Fin h ⊕ Fin h → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), ((τ).IsSymm ∧ ((τ).map Complex.im).PosDef) → (∀ x y, Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd (m x) (m y) : ℂ) / k) = em (b.ζ : o) ^ omegaStd x y) → (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i u => m (bas (Pi.single i 1) u)) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → SharpClass W a bas em t := by
  intro laws laws2 hc hT o _ g k J b em w w' h W a bas σ EF _ _ hw _ hEF t τ m Q Hm ⟨hs, hp⟩ hm hQ
    ⟨_, _, Qspan, _, _, hQim⟩ ⟨u, χ', hAH, hΛ, hχ, hpt, hact⟩
  obtain ⟨Ef₀, hEf₀, hbij⟩ := exists_form hs hp
  obtain ⟨P₀, u₀, χ₀, hg, hΛ₀, hAH₀, -, -⟩ := principalTorus_algebraic h _ (imInv τ) Ef₀ (per_lattice hs hp).2.1
    (per_lattice hs hp).2.2 (imInv_isHermitian hp) (imInv_pos hp) hEf₀ hbij
  subst hg
  let R : Fin 8 → (Fin g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ) := fun i => LinearMap.funLeft ℂ ℂ fun j => σ (i, j)
  have hRQ : ∀ i x, R i (Q x) = per τ (x i) := fun i x => funext fun j => hQ x i j
  have hmem : ∀ x, per τ x ∈ u₀.Λ := fun x => hΛ₀ ▸ ⟨x, rfl⟩
  have hΛ' : ∀ z, z ∈ u.Λ ↔ ∀ i, (fun j => z (σ (i, j))) ∈ u₀.Λ := fun z => by
    rw [hΛ, hΛ₀]
    constructor
    · rintro ⟨x, rfl⟩ i
      exact ⟨x i, (hRQ i x).symm⟩
    · intro H
      choose x hx using H
      refine ⟨x, funext fun c => ?_⟩
      obtain ⟨⟨i, j⟩, rfl⟩ := σ.surjective c
      exact (hQ x i j).trans (congrFun (hx i) j)
  obtain ⟨pr, hpr, hpru, hprod⟩ := exists_proj laws laws2 hc hT t.pol P₀ u u₀ σ hΛ'
  change Fin 8 → (t.A ⟶ P₀.A) at pr
  change ∀ i, IsMonHom (pr i : t.A ⟶ P₀.A) at hpr
  change ∀ (T : Over (Sp ℂ)) (y : Fin 8 → (T ⟶ P₀.A)), ∃! x : T ⟶ t.A, ∀ i, x ≫ pr i = y i at hprod
  change ∀ i z, u₀.ex (R i z) = u.ex z ≫ pr i at hpru
  have hk : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun e => hk (by simp [e])
  obtain ⟨Ef, hEf, -, -, -, -, -, -, hWeil⟩ := GlobalTheory.T.appellHumbert_uniformisation_riemannForm laws laws2 hc hT P₀ u₀ _ χ₀ hAH₀
  obtain ⟨c, φ, hφ, hcP, ⟨wP, hwP⟩, hlev⟩ := GlobalTheory.T.exists_siegPre_iso_of_polAV laws hc o ℂ em P₀.g k b.ζ (Units.map (em : o →* ℂ) b.ζ) P₀
    (fun x => u₀.ex ((k : ℂ)⁻¹ • per τ (m x))) rfl hk rfl
    (IsPrimitiveRoot.coe_units_iff.1 (b.prim ℂ em))
    (fun x y => by rw [map_add (f := _), map_add (f := _), smul_add, u₀.ex_add])
    (fun x => by
      rw [← ex_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hk, one_smul, u₀.ker]
      exact hmem _)
    (fun x y => hWeil k ⟨_, hmem (m x)⟩ ⟨_, hmem (m y)⟩ _ hk0 (by
      have e : Ef ⟨_, hmem (m x)⟩ ⟨_, hmem (m y)⟩ = omegaStd (m x) (m y) := by
        have := hEf ⟨_, hmem (m x)⟩ ⟨_, hmem (m y)⟩
        rw [im_hermForm_per hs hp] at this
        exact_mod_cast this
      rw [e, hm]
      simp))
  have hform : ∀ z z', hermForm Hm z z' =
      ∑ i, ∑ j, ((W + W.transpose) i j : ℂ) * hermForm (imInv τ) (R i z) (R j z') :=
    hermForm_eq_sum Hm (imInv τ) (W + W.transpose) R _ Qspan (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      simp only [hQim, hEF, hRQ, im_hermForm_per hs hp, Int.cast_sum, Int.cast_mul])
  have hchi : ∀ l : u.Λ, χ' l = Complex.exp (Real.pi * Complex.I *
      ∑ i, ∑ j, (W i j : ℂ) * ((hermForm (imInv τ) (R i l) (R j l)).im : ℂ)) := fun l => by
    obtain ⟨x, hx⟩ := (hΛ l).1 l.2
    rw [hχ x l hx.symm, hEF, form_act, hw, ← exp_pi_I_int, ← hx]
    simp [hRQ, im_hermForm_per hs hp]
  have hL := GlobalTheory.T.lbIso_linComb_lam_of_appellHumbert_alt laws laws2 hc hT W t.pol u Hm χ' P₀ u₀ _ χ₀ pr R hAH hAH₀ hpru hform hchi
  letI := P₀.isAb.comm
  haveI := hpr
  refine ⟨c, hcP, fun i => pr i ≫ φ.inv, fun i => inferInstanceAs (IsMonHom (pr i ≫ φ.inv)), fun T y => ?_, ?_, fun j i => ?_, fun i v => ?_⟩
  · simp only [← Category.assoc, Iso.comp_inv_eq]
    exact hprod T fun i => y i ≫ φ.hom
  · have hLam : (abelian₂ P₀.A P₀.L).IsLB := DVR.linComb_isLB _ P₀.isLB _ _
    refine LBIso.trans t.isLB (DVR.linComb_isLB _ hLam _ _) (DVR.linComb_isLB _ c.isLB _ _) hL (LBIso.symm ?_)
    have := iso_linComb ((isGen_iff wP).1 hwP) (K := Fin 8 × Fin 8)
      (fun uv => (lift (pr uv.1 ≫ φ.inv) (pr uv.2 ≫ φ.inv)).left) (fun uv => W uv.1 uv.2)
    simp only [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] at this
    exact this
  · obtain ⟨F, hF, hFa⟩ := hact j
    haveI := t.hom j
    have hRF : ∀ z, R i (F z) = ∑ v, a j i v • R v z := fun z => by
      have : ((R i ∘ₗ F).restrictScalars ℝ) = (∑ v, a j i v • R v).restrictScalars ℝ :=
        LinearMap.ext_on_range Qspan fun x => by
          rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, LinearMap.comp_apply, hF, hRQ,
            LinearMap.sum_apply]
          simp only [LinearMap.smul_apply, hRQ]
          exact (map_sum (per τ) _ _).trans (Finset.sum_congr rfl fun v _ => map_zsmul (per τ) _ _)
      simpa using LinearMap.congr_fun this z
    have e1 : ∀ z, u₀.ex (R i (F z)) = u.ex z ≫ t.act j ≫ pr i := fun z => by
      rw [hpru, hFa, Category.assoc]
    have e2 : ∀ z, u₀.ex (R i (F z)) = u.ex z ≫ ∏ v, pr v ^ a j i v := fun z => by
      rw [hRF, ex_sum, PowMatrixLinear.comp_prod]
      simp only [ex_zsmul, hpru, GrpObj.comp_zpow]
    have e : t.act j ≫ pr i = ∏ v, pr v ^ a j i v :=
      hom_ext_of_lin laws laws2 hc hT t.pol P₀ u u₀ (R i ∘ₗ F) _ _ e1 e2
        (inferInstanceAs (IsMonHom (t.act j ≫ pr i)))
    rw [← Category.assoc, e, PowMatrixLinear.prod_comp]
    simp only [GrpObj.zpow_comp]
    exact (List.prod_ofFn).symm
  · rw [Over.comp_left, hpt, ← Over.comp_left, ← Category.assoc, ← hpru, map_smul, hRQ, ← hlev, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerThetaObjectOfUniformisationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.eighthPower_theta_object_of_uniformisation : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (σ : Fin 8 × Fin h ≃ Fin g) (EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ x y, EF x y = ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (x u) (y v)) → ∀ (t : TObj g k J b (spMap em)) (τ : Matrix (Fin h) (Fin h) ℂ) (m : (Fin h ⊕ Fin h → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), ((τ).IsSymm ∧ ((τ).map Complex.im).PosDef) → (∀ x y, Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd (m x) (m y) : ℂ) / k) = em (b.ζ : o) ^ omegaStd x y) → (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i u => m (bas (Pi.single i 1) u)) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → SharpClass W a bas em t := by
  first | exact @GlobalTheory.sharpClass_of_unif | exact GlobalTheory.sharpClass_of_unif | (intros; apply GlobalTheory.sharpClass_of_unif <;> assumption)
end
end
