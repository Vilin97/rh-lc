module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.BarOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.ConjHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.DerPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Kill0
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.LcMat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.StarFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.TrRep
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Imports

section

@[expose] public section

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.kill :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} [IsDomain O] {G : Type} [Group G] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (τ : MonoidAlgebra R G → R) (c c₀ : O) (d : MonoidAlgebra R G →+ Matrix (Fin n) (Fin n) X), c₀ ≠ 0 → (∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) → (∀ y, (repR x ρ y).trace = x (τ y)) → IsLift x δ (repR x ρ) τ c d → ∀ y, (∀ g, τ ((MonoidAlgebra.single g 1) * y) = 0) → repR x ρ y = 0 ∧ c₀ • d y = 0 := by
  intro O R X _ _ _ _ _ n _ G _ x δ ρ τ c c₀ d hc₀ hspan htr hd y hy
  obtain ⟨k1, k2⟩ := kill0 ρ c₀ hc₀ hspan
  have hs : ∀ g : G, repR x ρ (MonoidAlgebra.single g 1) = ρ g := by
    intro g
    rw [repR_single, map_one, one_smul]
  have h1 : repR x ρ y = 0 := by
    apply k1
    intro g
    rw [← hs, ← map_mul, htr, hy, map_zero]
  refine ⟨h1, k2 X (d y) ?_⟩
  intro g
  have e := hd.mul (MonoidAlgebra.single g 1) y
  rw [h1, hs] at e
  have hb0 : bar X (0 : Matrix (Fin n) (Fin n) O) = 0 := by
    ext i j
    simp [bar]
  rw [hb0, Matrix.mul_zero, zero_add] at e
  rw [← e, hd.tr, hy, map_zero, smul_zero]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Polar

section

@[expose] public section

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.polar :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} [Algebra ℤ_[l] O] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : F.G₀ →* GL (Fin n) O) (P : GL (Fin n) O) (t : MonoidAlgebra R F.G₀ →ₗ[R] R) (c : O) (d : MonoidAlgebra R F.G₀ →+ Matrix (Fin n) (Fin n) X), ((P : Matrix (Fin n) (Fin n) O)ᵀ = P ∨ (P : Matrix (Fin n) (Fin n) O)ᵀ = -P) → F.IsForm O n ρ P → (∀ g, t (F.star O R n (MonoidAlgebra.single g 1)) = t (MonoidAlgebra.single g 1)) → IsLift x δ (repR x (mat ρ)) t c d → ∃ d' : MonoidAlgebra R F.G₀ →+ Matrix (Fin n) (Fin n) X, IsLift x δ (repR x (mat ρ)) t (2 * c) d' ∧ ∀ a, bar X (P : Matrix (Fin n) (Fin n) O) * d' (F.star O R n a) = (d' a)ᵀ * bar X (P : Matrix (Fin n) (Fin n) O) := by
  intro l _ F O R X _ _ _ _ _ n _ x δ ρ P t c d hP hF ht hd
  obtain ⟨hsm, hsa, hsr, hss, -, hsρ⟩ := starFacts F (O := O) (R := R) (n := n)
  have hρs := hsρ x ρ P hF
  obtain ⟨ε, hεε, hPt⟩ : ∃ ε : O, ε * ε = 1 ∧
      (P : Matrix (Fin n) (Fin n) O)ᵀ = ε • (P : Matrix (Fin n) (Fin n) O) := by
    rcases hP with h | h
    · exact ⟨1, one_mul 1, by rw [h, one_smul]⟩
    · exact ⟨-1, by ring, by rw [h, neg_one_smul]⟩
  have hmap : ∀ A B : Matrix (Fin n) (Fin n) O, bar X (A * B) = bar X A * bar X B :=
    fun A B => Matrix.map_mul
  set Pb := bar X (P : Matrix (Fin n) (Fin n) O) with hPb
  set Q := bar X ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) with hQ
  set e : X := algebraMap O X ε with he
  have hQP : Q * Pb = 1 := by
    rw [hQ, hPb, ← hmap, Units.inv_mul]
    simp [bar]
  have hPQ : Pb * Q = 1 := by
    rw [hQ, hPb, ← hmap, Units.mul_inv]
    simp [bar]
  have hQP' : ∀ M, Q * (Pb * M) = M := fun M => by rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hPQ' : ∀ M, Pb * (Q * M) = M := fun M => by rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hee : e * e = 1 := by rw [he, ← map_mul, hεε, map_one]
  have hPbt : Pbᵀ = e • Pb := by
    ext i j
    have h := congrFun (congrFun hPt i) j
    simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] at h
    simp [hPb, bar, Matrix.transpose_apply, h, map_mul, he]
  have hQt : Qᵀ = e • Q := by
    have h0 : e • (Pb * Qᵀ) = 1 := by
      rw [← Matrix.smul_mul, ← hPbt, ← Matrix.transpose_mul, hQP, Matrix.transpose_one]
    have h1 : Pb * Qᵀ = e • 1 := by
      calc Pb * Qᵀ = (e * e) • (Pb * Qᵀ) := by rw [hee, one_smul]
        _ = e • 1 := by rw [mul_smul, h0]
    calc Qᵀ = Q * (Pb * Qᵀ) := by rw [hQP']
      _ = e • Q := by rw [h1, Matrix.mul_smul, Matrix.mul_one]
  have hρ : ∀ a, bar X (repR x (mat ρ) (F.star O R n a)) =
      Q * (bar X (repR x (mat ρ) a))ᵀ * Pb := by
    intro a
    rw [hρs, hmap, hmap]
    rfl
  have hρT : ∀ a, (bar X (repR x (mat ρ) (F.star O R n a)))ᵀ =
      Pb * bar X (repR x (mat ρ) a) * Q := by
    intro a
    rw [hρ, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hPbt, hQt]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hee, one_smul, Matrix.mul_assoc]
  let eD : MonoidAlgebra R F.G₀ →+ Matrix (Fin n) (Fin n) X :=
    AddMonoidHom.mk' (fun a => Q * (d (F.star O R n a))ᵀ * Pb) (by
      intro a b
      simp only [hsa, map_add (f := _), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul])
  have heD : ∀ a, eD a = Q * (d (F.star O R n a))ᵀ * Pb := fun a => rfl
  have h0 : F.star O R n 0 = 0 := by simpa using hsr 0 0
  have htS : ∀ a, t (F.star O R n a) = t a := by
    intro a
    induction a using MonoidAlgebra.induction_linear with
    | zero => rw [h0]
    | add a b ha hb => rw [hsa, map_add (f := _), map_add (f := _), ha, hb]
    | single g r =>
      have hs : (MonoidAlgebra.single g r : MonoidAlgebra R F.G₀) = r • MonoidAlgebra.single g 1 := by
        rw [MonoidAlgebra.smul_single', mul_one]
      rw [hs, hsr, map_smul, map_smul, ht]
  refine ⟨d + eD, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a b
    simp only [AddMonoidHom.add_apply, heD, hd.mul, hsm, Matrix.transpose_add, Matrix.transpose_mul,
      hρT, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hQP', hQP, Matrix.mul_one]
    abel
  · intro r a
    simp only [AddMonoidHom.add_apply, heD, hd.smul, hsr, Matrix.transpose_add, Matrix.transpose_smul,
      hρT, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hQP',
      hQP, Matrix.mul_one, smul_add, two_mul, add_smul]
    abel
  · intro a
    rw [AddMonoidHom.add_apply, Matrix.trace_add, hd.tr, heD, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      hPQ, Matrix.one_mul, Matrix.trace_transpose, hd.tr, htS, two_mul, add_smul]
  · intro a
    simp only [AddMonoidHom.add_apply, heD, hss, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose, hPbt, hQt, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hee, one_smul, Matrix.mul_assoc, hPQ', hPQ, hQP, hQP', Matrix.mul_one]
    abel
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.ZOf

section

@[expose] public section

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.zOf :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} [Algebra ℤ_[l] O] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : F.G₀ →* GL (Fin n) O) (P : GL (Fin n) O) (τ : MonoidAlgebra R F.G₀ → R) (c : O) (d : MonoidAlgebra R F.G₀ →+ Matrix (Fin n) (Fin n) X) (z : F.G₀ → Matrix (Fin n) (Fin n) X), IsDer x δ → F.IsForm O n ρ P → IsLift x δ (repR x (mat ρ)) τ c d → (∀ a, bar X (P : Matrix (Fin n) (Fin n) O) * d (F.star O R n a) = (d a)ᵀ * bar X (P : Matrix (Fin n) (Fin n) O)) → (∀ g, z g = d (MonoidAlgebra.single g 1) * bar X (mat ρ g⁻¹)) → d 1 = 0 ∧ (∀ g g', z (g * g') = z g + bar X (mat ρ g) * z g' * bar X (mat ρ g⁻¹)) ∧ (∀ g, bar X (P : Matrix (Fin n) (Fin n) O) * z (F.conj g) = -((z g)ᵀ * bar X (P : Matrix (Fin n) (Fin n) O))) ∧ ∀ g, (z g * bar X (mat ρ g)).trace = c • δ (τ (MonoidAlgebra.single g 1)) := by
  intro l _ F O R X _ _ _ _ _ n _ x δ ρ P τ c d z hδ hF hL hst hz
  have bmul : ∀ A B : Matrix (Fin n) (Fin n) O, bar X (A * B) = bar X A * bar X B := fun A B => Matrix.map_mul
  have bone : bar X (1 : Matrix (Fin n) (Fin n) O) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have bsm : ∀ (e : O) (A : Matrix (Fin n) (Fin n) O), bar X (e • A) = e • bar X A := by
    intro e A
    ext i j
    show algebraMap O X (e * A i j) = e • algebraMap O X (A i j)
    rw [map_mul, Algebra.smul_def]
  have rmul : ∀ g g', bar X (mat ρ (g * g')) = bar X (mat ρ g) * bar X (mat ρ g') := by
    intro g g'
    rw [map_mul, bmul]
  have rinv : ∀ g, bar X (mat ρ g⁻¹) * bar X (mat ρ g) = 1 := by
    intro g
    rw [← rmul, inv_mul_cancel, map_one, bone]
  have rinv' : ∀ g, bar X (mat ρ g) * bar X (mat ρ g⁻¹) = 1 := by
    intro g
    rw [← rmul, mul_inv_cancel, map_one, bone]
  have d1 : d 1 = 0 := by
    have h := hL.mul 1 1
    rw [mul_one, map_one (repR x (mat ρ)), bone, mul_one, one_mul] at h
    exact left_eq_add.mp h
  have δ1 : δ 1 = 0 := by
    have h := hδ 1 1
    rw [mul_one, map_one x, one_smul] at h
    exact left_eq_add.mp h
  have δa : ∀ e : O, δ (algebraMap O R e) = 0 := by
    intro e
    rw [Algebra.algebraMap_eq_smul_one, map_smul, δ1, smul_zero]
  have dmul : ∀ g g', d (MonoidAlgebra.single (g * g') 1) =
      d (MonoidAlgebra.single g 1) * bar X (mat ρ g') + bar X (mat ρ g) * d (MonoidAlgebra.single g' 1) := by
    intro g g'
    have h := hL.mul (MonoidAlgebra.single g 1) (MonoidAlgebra.single g' 1)
    rw [MonoidAlgebra.single_mul_single, mul_one, repR_single, repR_single, map_one, one_smul, one_smul] at h
    exact h
  have hd : ∀ g, d (MonoidAlgebra.single g 1) = z g * bar X (mat ρ g) := by
    intro g
    rw [hz, mul_assoc, rinv, mul_one]
  have dinv : ∀ g, d (MonoidAlgebra.single g⁻¹ 1) = -(bar X (mat ρ g⁻¹) * z g) := by
    intro g
    have h := dmul g⁻¹ g
    rw [inv_mul_cancel, ← MonoidAlgebra.one_def, d1] at h
    have h2 := congrArg (· * bar X (mat ρ g⁻¹)) h
    simp only [zero_mul, add_mul, mul_assoc, rinv', mul_one] at h2
    rw [hz]
    exact eq_neg_of_add_eq_zero_left h2.symm
  refine ⟨d1, ?_, ?_, ?_⟩
  · intro g g'
    rw [hz (g * g'), dmul, _root_.mul_inv_rev, rmul, hz g, hz g', add_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (bar X (mat ρ g')), rinv', one_mul]
  · intro g
    have h := hst (MonoidAlgebra.single g 1)
    rw [(starFacts F (O := O) (R := R) (n := n)).2.2.2.2.1 g] at h
    have hf := congrArg (bar X) (hF g)
    generalize ((F.eps O O g ^ (1 - (n : ℤ)) : Oˣ) : O) = e at h hf
    have hs : (MonoidAlgebra.single (F.conj g)⁻¹ (algebraMap O R e) : MonoidAlgebra R F.G₀) =
        algebraMap O R e • MonoidAlgebra.single (F.conj g)⁻¹ 1 := by
      rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [hs, hL.smul, δa, smul_zero, zero_smul, add_zero, AlgHom.commutes, dinv, hd, transpose_mul] at h
    rw [bmul, bmul, bsm] at hf
    have ht : bar X (mat ρ g)ᵀ = (bar X (mat ρ g))ᵀ := rfl
    rw [ht] at hf
    have hf2 : (bar X (mat ρ g))ᵀ * bar X (P : Matrix (Fin n) (Fin n) O) =
        e • (bar X (P : Matrix (Fin n) (Fin n) O) * bar X (mat ρ (F.conj g)⁻¹)) := by
      rw [← smul_mul_assoc, ← hf, mul_assoc, rinv', mul_one]
    have h3 : (bar X (mat ρ g))ᵀ * (bar X (P : Matrix (Fin n) (Fin n) O) * z (F.conj g)) =
        (bar X (mat ρ g))ᵀ * -((z g)ᵀ * bar X (P : Matrix (Fin n) (Fin n) O)) := by
      rw [mul_neg, ← mul_assoc, ← mul_assoc, ← h, hf2]
      simp [mul_assoc]
    have h4 : (bar X (mat ρ g⁻¹))ᵀ * (bar X (mat ρ g))ᵀ = 1 := by
      rw [← transpose_mul, rinv', transpose_one]
    have h5 := congrArg ((bar X (mat ρ g⁻¹))ᵀ * ·) h3
    simp only [← mul_assoc _ (bar X (mat ρ g))ᵀ, h4, one_mul] at h5
    exact h5
  · intro g
    rw [← hd, hL.tr]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.LiftSmul

section

@[expose] public section

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem lift_smul {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ}
    {E : Type} [Ring E] [Algebra R E] {x : R →ₐ[O] O} {δ : R →ₗ[O] X} {ρ : E →+* Matrix (Fin n) (Fin n) O}
    {τ : E → R} {c : O} {d : E →+ Matrix (Fin n) (Fin n) X} (h : IsLift x δ ρ τ c d) (a : O) :
    IsLift x δ ρ τ (a * c) (a • d) := by
  constructor
  · intro u v
    simp only [AddMonoidHom.smul_apply, h.mul, smul_add, Matrix.smul_mul, Matrix.mul_smul]
  · intro r u
    simp only [AddMonoidHom.smul_apply, h.smul, smul_add]
    rw [smul_comm a (x r), mul_smul, smul_assoc a]
  · intro u
    simp only [AddMonoidHom.smul_apply, Matrix.trace_smul, h.tr, mul_smul]

private theorem lc_mat {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
  have : ∀ᶠ g' in nhds g, ∀ i j, f g' i j = f g i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq g
  exact this.mono fun g' e => Matrix.ext e

private theorem der_const {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X] [Module O X] {x : R →ₐ[O] O}
    {δ : R →ₗ[O] X} (h : IsDer x δ) (a : O) : δ (algebraMap O R a) = 0 := by
  have h1 := h 1 1
  rw [mul_one, map_one x, one_smul] at h1
  have h2 : δ 1 = 0 := by simpa using h1
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h2, smul_zero]

theorem UpperTheory.V.Th.coc :
    Coc := by
  intro l hl L G0 n O _ _ _ hO _ y h2 hn
  classical
  obtain ⟨c₀, hc₀, hsp⟩ := y.span
  choose c₁ hc₁ hloc using fun v => locAt y v
  have h2O : (2 : O) ≠ 0 := by
    intro e
    haveI := hO.char
    have h3 : ((2 : ℕ) : ResidueField O) = 0 := by
      rw [← map_natCast (residue O), Nat.cast_ofNat, e, map_zero]
    exact h2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff _ l 2).1 h3))
  refine ⟨(∏ v, c₁ v) * (c₀ * (2 * (c₀ ^ (2 * n) * c₀ ^ (2 * n)))),
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun v _ => hc₁ v) (mul_ne_zero hc₀ (mul_ne_zero h2O
      (mul_ne_zero (pow_ne_zero _ hc₀) (pow_ne_zero _ hc₀)))), ?_⟩
  intro G h rN R _ _ _ p x hI hp m δ hδ
  have hsurj : Function.Surjective h.p₀ := fun g => by
    obtain ⟨g', e⟩ := h.surj g
    exact ⟨⟨g', by rw [MonoidHom.mem_ker, ← h.η, e]; exact g.2⟩, Subtype.ext e⟩
  have hcont : Continuous h.p₀ := (h.cont.comp continuous_subtype_val).subtype_mk _
  have hsp' : ∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range (mat (y.ρ.comp h.p₀))) := fun Z => by
    have e : Set.range (mat (y.ρ.comp h.p₀)) = Set.range (mat y.ρ) := hsurj.range_comp (mat y.ρ)
    rw [e]
    exact hsp Z
  have hform : G.frame.IsForm O n (y.ρ.comp h.p₀) y.P := fun g => by
    have e1 : h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := Subtype.ext (by
      change h.p (G.c * g * G.c⁻¹) = G0.c * h.p g * G0.c⁻¹
      rw [map_mul, map_mul, map_inv, h.c])
    have e2 : G.frame.eps O O g = G0.frame.eps O O (h.p₀ g) := by
      change Units.map _ (G.ε g) = Units.map _ (G0.ε (h.p g))
      rw [h.ε]
    have := y.form (h.p₀ g)
    rw [← e1, ← e2] at this
    exact this
  obtain ⟨htr, -, t, ht⟩ := trRep p.D x _ hn hp.1
  have ht' : (t : _ → R) = p.D.tr := funext ht
  obtain ⟨d1, hd1⟩ := liftG p.D rN.chib x δ _ c₀ hn rN.chib_inj p.red hp.1 hc₀ hsp' hδ
  obtain ⟨d2, hd2, hpol⟩ := polar G.frame x δ _ y.P t _ d1 y.sgn hform (fun g => by rw [ht, ht]; exact p.P 1 g) (ht' ▸ hd1)
  rw [ht'] at hd2
  have hk := kill x δ _ _ _ c₀ d2 hc₀ hsp' htr hd2
  have hd3 := lift_smul hd2 c₀
  have hd4 := lift_smul hd3 (∏ v, c₁ v)
  obtain ⟨h1, hcoc, hP, hT⟩ := zOf G.frame x δ _ y.P _ _ _
    (fun g => ((∏ v, c₁ v) • c₀ • d2) (MonoidAlgebra.single g 1) * bar (Om O m) (mat (y.ρ.comp h.p₀) g⁻¹)) hδ hform hd4
    (fun a => by simp only [AddMonoidHom.smul_apply, Matrix.mul_smul, Matrix.transpose_smul, Matrix.smul_mul, hpol]) fun _ => rfl
  have hρlc : IsLocallyConstant fun g => bar (Om O m) (mat (y.ρ.comp h.p₀) g) :=
    (lc_mat _ fun i j => (lcDer (R := R) m).1 _ (y.cont i j)).comp_continuous hcont
  refine ⟨_, ⟨?_, hcoc, hP, fun u g hg => ?_, fun v => ?_⟩, hT⟩
  · have hl2 := lc x δ _ _ _ c₀ d2 hsp' hd2 hρlc ((lcDer m).2 x δ hδ _ (p.cont 1))
    exact (hl2.comp fun Z => (∏ v, c₁ v) • Z).mul (hρlc.comp_continuous continuous_inv)
  · have h4 := (hk _ (p.I u g (hI u ▸ hg))).2
    have h5 : d2 1 = 0 := by
      have := hd2.mul 1 1
      simpa using this
    rw [map_sub, h5, sub_zero] at h4
    simp only [AddMonoidHom.smul_apply, h4, smul_zero, Matrix.zero_mul]
  · obtain ⟨Y, hY⟩ := hloc v G h R x m δ _ _ _ (p.ψ v) hd3
      (fun i g => congrArg Units.val (DFunLike.congr_fun (hp.2 v i) g))
      (fun g => hk _ (p.Ord v g)) fun i g hg => by
        rw [(p.psi v i).mu ⟨g, hg⟩]
        exact der_const hδ _
    refine ⟨(∏ v' ∈ Finset.univ.erase v, c₁ v') • Y, fun g => ?_⟩
    have e : ((∏ v, c₁ v) • c₀ • d2) (MonoidAlgebra.single (G.frame.φ v g) 1) *
          bar (Om O m) (mat (y.ρ.comp h.p₀) (G.frame.φ v g)⁻¹) -
        dY G.frame (y.ρm h m) ((∏ v' ∈ Finset.univ.erase v, c₁ v') • Y) (G.frame.φ v g) =
        (∏ v' ∈ Finset.univ.erase v, c₁ v') • (c₁ v • ((c₀ • d2) (MonoidAlgebra.single (G.frame.φ v g) 1) *
          y.ρm h m (G.frame.φ v g)⁻¹) - dY G.frame (y.ρm h m) Y (G.frame.φ v g)) := by
      rw [smul_sub, smul_smul (∏ v' ∈ Finset.univ.erase v, c₁ v'), Finset.prod_erase_mul _ _ (Finset.mem_univ v),
        AddMonoidHom.smul_apply, Matrix.smul_mul]
      simp only [dY, smul_sub, Matrix.mul_smul, Matrix.smul_mul]
      rfl
    rw [e]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply]
    refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
    · have := (hY g).1 i j hij
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply] at this
      rw [this, smul_zero]
    · have := (hY g).2 hg i
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply] at this
      rw [this, smul_zero]
end
end
