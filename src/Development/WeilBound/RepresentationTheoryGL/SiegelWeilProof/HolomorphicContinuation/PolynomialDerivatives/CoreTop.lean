module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullStableAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.BoxLeFirstFamily
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoeffSmulX
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.ZeroRight
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.SupPerp
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FirstFamilySymbolMulVariablePow
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.SymmetricFiltrationIffSupported
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.TransvectionInv
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.KAlgOfAdjoinRestrict
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PderivPowMonomial
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.ProdMapPowSingle
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.SecondOperatorMemSecondFamily
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.SupPerp

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.DiagApply

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Rg.Sw.LC

namespace CoreA

variable {V : Type} [AddCommGroup V] [Module ℂ V] {φ : V → V → ℂ}

theorem adj_closed (h : PosH φ) {ι : Type} (T : ι → Module.End ℂ V)
    (hT : ∀ i, ∃ j, ∀ v w, φ (T i v) w = φ v (T j w)) :
    ∀ s ∈ Algebra.adjoin ℂ (Set.range T), ∃ s' ∈ Algebra.adjoin ℂ (Set.range T), ∀ v w, φ (s v) w = φ v (s' w) := by
  intro s hs
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, hj⟩ := hT i
    exact ⟨T j, Algebra.subset_adjoin ⟨j, rfl⟩, hj⟩
  | algebraMap r =>
    refine ⟨algebraMap ℂ _ (star r), Subalgebra.algebraMap_mem _ _, fun v w => ?_⟩
    simp only [Module.algebraMap_end_apply]
    rw [h.smul_left, h.smul]
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', hx''⟩ := hx
    obtain ⟨y', hy', hy''⟩ := hy
    refine ⟨x' + y', add_mem hx' hy', fun v w => ?_⟩
    simp only [LinearMap.add_apply]
    rw [h.add_left, hx'', hy'', h.add]
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', hx''⟩ := hx
    obtain ⟨y', hy', hy''⟩ := hy
    refine ⟨y' * x', mul_mem hy' hx', fun v w => ?_⟩
    simp only [Module.End.mul_apply]
    rw [hx'', hy'']

theorem orbit [FiniteDimensional ℂ V] (h : PosH φ) {ι : Type} (T : ι → Module.End ℂ V)
    (hT : ∀ i, ∃ j, ∀ v w, φ (T i v) w = φ v (T j w)) (x : Module.End ℂ V)
    (hx : ∀ t : Module.End ℂ V, (∀ i, t * T i = T i * t) → x * t = t * x) (v : V) :
    ∃ s ∈ Algebra.adjoin ℂ (Set.range T), x v = s v := by
  classical
  set S := Algebra.adjoin ℂ (Set.range T) with hS
  let M : Submodule ℂ V := (Subalgebra.toSubmodule S).map (LinearMap.applyₗ v)
  have hM : ∀ y, y ∈ M ↔ ∃ s ∈ S, s v = y := by
    intro y
    simp [M, Submodule.mem_map]
  have hMinv : ∀ s ∈ S, ∀ y ∈ M, s y ∈ M := by
    intro s hs y hy
    obtain ⟨t, ht, rfl⟩ := (hM y).1 hy
    exact (hM _).2 ⟨s * t, mul_mem hs ht, rfl⟩
  have hNinv : ∀ s ∈ S, ∀ u ∈ h.perp M, s u ∈ h.perp M := by
    intro s hs u hu m hm
    obtain ⟨s', hs', hs''⟩ := adj_closed h T hT s hs
    rw [h.herm (s u) m, hs'' u m, h.herm (s' m) u, star_star, hu _ (hMinv s' hs' m hm)]
  have hc : IsCompl M (h.perp M) := IsCompl.of_eq (h.inf_perp M) (h.sup_perp M)
  let P : Module.End ℂ V := M.subtype ∘ₗ Submodule.projectionOnto M (h.perp M) hc
  have hPdec : ∀ m ∈ M, ∀ u ∈ h.perp M, P (m + u) = m := by
    intro m hm u hu
    have e1 : Submodule.projectionOnto M (h.perp M) hc m = ⟨m, hm⟩ :=
      Submodule.projectionOnto_apply_left hc ⟨m, hm⟩
    have e2 : Submodule.projectionOnto M (h.perp M) hc u = 0 :=
      Submodule.projectionOnto_apply_right hc ⟨u, hu⟩
    simp only [P, LinearMap.comp_apply, map_add (f := _), e1, e2]
    simp
  have hdec : ∀ y : V, ∃ m ∈ M, ∃ u ∈ h.perp M, y = m + u := by
    intro y
    have hy : y ∈ M ⊔ h.perp M := by rw [h.sup_perp]; trivial
    obtain ⟨m, hm, u, hu, e⟩ := Submodule.mem_sup.1 hy
    exact ⟨m, hm, u, hu, e.symm⟩
  have hPT : ∀ i, P * T i = T i * P := by
    intro i
    have hTi : T i ∈ S := Algebra.subset_adjoin ⟨i, rfl⟩
    refine LinearMap.ext fun y => ?_
    obtain ⟨m, hm, u, hu, rfl⟩ := hdec y
    simp only [Module.End.mul_apply]
    rw [map_add (T i), hPdec _ (hMinv _ hTi m hm) _ (hNinv _ hTi u hu), hPdec m hm u hu]
  have hxP := hx P hPT
  have hvM : v ∈ M := (hM v).2 ⟨1, Subalgebra.one_mem S, rfl⟩
  have hPv : P v = v := by simpa using hPdec v hvM 0 (Submodule.zero_mem _)
  have hxv : x v = P (x v) := by
    rw [← Module.End.mul_apply, ← hxP, Module.End.mul_apply, hPv]
  have hmem : P (x v) ∈ M := by
    simp only [P, LinearMap.comp_apply, Submodule.subtype_apply]
    exact Submodule.coe_mem _
  obtain ⟨s, hs, hsv⟩ := (hM _).1 hmem
  exact ⟨s, hs, by rw [hxv, ← hsv]⟩

def diag (d : ℕ) : Module.End ℂ V →ₐ[ℂ] Module.End ℂ (Fin d → V) where
  toFun f := LinearMap.pi fun k => f ∘ₗ LinearMap.proj k
  map_one' := LinearMap.ext fun w => funext fun k => by simp
  map_mul' f g := LinearMap.ext fun w => funext fun k => by simp
  map_zero' := LinearMap.ext fun w => funext fun k => by simp
  map_add' f g := LinearMap.ext fun w => funext fun k => by simp
  commutes' r := LinearMap.ext fun w => funext fun k => by simp

theorem diag_apply (d : ℕ) (f : Module.End ℂ V) (w : Fin d → V) (k : Fin d) : diag d f w k = f (w k) := by
  simp [diag]

def amp (φ : V → V → ℂ) (d : ℕ) (v w : Fin d → V) : ℂ := ∑ k, φ (v k) (w k)

theorem amp_posH (h : PosH φ) (d : ℕ) : PosH (amp φ d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v w₁ w₂
    simp only [amp, Pi.add_apply, h.add, Finset.sum_add_distrib]
  · intro v w r
    simp only [amp, Pi.smul_apply, h.smul, Finset.mul_sum]
  · intro v w
    simp only [amp, star_sum, ← h.herm]
  · intro v hv
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
    simp only [amp, Complex.re_sum]
    calc 0 < (φ (v k) (v k)).re := h.pos _ hk
      _ ≤ ∑ l, (φ (v l) (v l)).re :=
        Finset.single_le_sum (f := fun l => (φ (v l) (v l)).re) (fun l _ => h.re_nonneg _) (Finset.mem_univ k)

end CoreA

open CoreA in
theorem bicomm : Bicomm := by
  intro V _ _ _ φ hadd hsmul hherm hpos ι T hT x hx
  classical
  have h : PosH φ := ⟨hadd, hsmul, hherm, hpos⟩
  set d := Module.finrank ℂ V
  let e := Module.finBasis ℂ V
  let T' : ι → Module.End ℂ (Fin d → V) := fun i => diag d (T i)
  have hT' : ∀ i, ∃ j, ∀ v w, amp φ d (T' i v) w = amp φ d v (T' j w) := by
    intro i
    obtain ⟨j, hj⟩ := hT i
    exact ⟨j, fun v w => by simp only [amp, T', diag_apply, hj]⟩
  have hx' : ∀ t : Module.End ℂ (Fin d → V), (∀ i, t * T' i = T' i * t) → diag d x * t = t * diag d x := by
    intro t ht
    let tt : Fin d → Fin d → Module.End ℂ V := fun k l => LinearMap.proj k ∘ₗ t ∘ₗ LinearMap.single ℂ (fun _ => V) l
    have htt : ∀ k l, x * tt k l = tt k l * x := by
      intro k l
      apply hx
      intro i
      refine LinearMap.ext fun u => ?_
      have hs : (Pi.single l (T i u) : Fin d → V) = T' i (Pi.single l u) := by
        funext l'
        simp only [T', diag_apply]
        by_cases hl : l' = l
        · subst hl; simp
        · simp [Pi.single_apply, hl]
      have := LinearMap.congr_fun (ht i) (Pi.single l u)
      simp only [Module.End.mul_apply] at this
      simp only [Module.End.mul_apply, tt, LinearMap.comp_apply, LinearMap.coe_single, LinearMap.coe_proj,
        Function.eval, hs, this]
      simp [T', diag_apply]
    have hsum : ∀ w : Fin d → V, ∀ k, t w k = ∑ l, tt k l (w l) := by
      intro w k
      conv_lhs => rw [← Finset.univ_sum_single w]

      simp [tt, map_sum]
    refine LinearMap.ext fun w => funext fun k => ?_

    simp only [Module.End.mul_apply, diag_apply, hsum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact LinearMap.congr_fun (htt k l) (w l)
  obtain ⟨s', hs', hs'E⟩ := orbit (amp_posH h d) T' hT' (diag d x) hx' (fun k => e k)
  have hmap : Algebra.adjoin ℂ (Set.range T') = (Algebra.adjoin ℂ (Set.range T)).map (diag d) := by
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  rw [hmap] at hs'
  obtain ⟨s, hs, rfl⟩ := Subalgebra.mem_map.1 hs'
  have hxs : x = s := by
    refine e.ext fun k => ?_
    have := congrFun hs'E k
    simpa [diag_apply] using this
  rw [hxs]
  exact hs

end PositivityTheory.Rg.Sw.LC
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.MapDomainInlInr

section

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ} {ε : Fin m → Bool}

theorem op_sum_f (u : Sym m n) {ι : Type*} (S : Finset ι) (c : ι → ℂ) (h : ι → PX m n) :
    op u (∑ i ∈ S, c i • h i) = ∑ i ∈ S, c i • op u (h i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [op_zero_f]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, op_add_f, op_smul_f, ih]

theorem kpow {a : Ix m n} (ha : inF1 ε a) (b : ℕ) : ∀ (d : ℕ) (u : Sym m n), SymbolInFirstFamily ε u → EtaLe u d →
    ∃ r, Good ε d r ∧ ∀ g, op u (X a ^ b * g) = op (u * X (Sum.inl a) ^ b) g + op r g := by
  induction b with
  | zero => intro d u _ _; exact ⟨0, good_zero d, fun g => by simp [op_zero]⟩
  | succ b ih =>
    intro d u hu hue
    obtain ⟨r₁, hr₁, e₁⟩ := ih d u hu hue
    have hdu := good_pderiv hu hue a
    obtain ⟨r₂, hr₂, e₂⟩ := ih d (pderiv (Sum.inr a) u) hdu.1 (good_le hdu)
    have hX : ∀ k, ((Finsupp.single (Sum.inl a) 1 : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) ≠ 0 ∨
        (Finsupp.single (Sum.inl a) 1 : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k := by
      intro k hk
      simp only [Finsupp.single_apply, Sum.inl.injEq, reduceCtorEq, if_false, ne_eq, not_true, or_false] at hk
      split_ifs at hk with h
      · subst h; exact ha
      · exact absurd rfl hk
    have hXb : ∀ k, ((Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) ≠ 0 ∨
        (Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k := by
      intro k hk
      simp only [Finsupp.single_apply, Sum.inl.injEq, reduceCtorEq, if_false, ne_eq, not_true, or_false] at hk
      split_ifs at hk with h
      · subst h; exact ha
      · exact absurd rfl hk
    have g1 : Good ε d (r₁ * X (Sum.inl a)) := by
      have := good_mul_monomial (e := 0) hr₁ _ hX (by simp [Finsupp.single_apply])
      simpa [X] using this
    have g2 : Good ε d (pderiv (Sum.inr a) u * X (Sum.inl a) ^ b) := by
      have := good_mul_monomial (e := 0) hdu _ hXb (by simp [Finsupp.single_apply])
      simpa [X_pow_eq_monomial] using this
    refine ⟨r₁ * X (Sum.inl a) + pderiv (Sum.inr a) u * X (Sum.inl a) ^ b + r₂, good_add (good_add g1 g2) hr₂, fun g => ?_⟩
    rw [pow_succ', mul_assoc, op_X_mul, e₁, e₂, op_add, op_add, op_mul_inl, pow_succ, ← mul_assoc, op_mul_inl]
    ring

theorem mapDomain_inl_inl (γ : Ix m n →₀ ℕ) (k : Ix m n) :
    (γ.mapDomain Sum.inl : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) = γ k :=
  Finsupp.mapDomain_apply_of_injective Sum.inl_injective γ k

theorem mapDomain_inl_inr (γ : Ix m n →₀ ℕ) (k : Ix m n) :
    (γ.mapDomain Sum.inl : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) = 0 :=
  Finsupp.mapDomain_notin_range γ _ (by simp)

theorem mapDomain_inr_inr (γ : Ix m n →₀ ℕ) (k : Ix m n) :
    (γ.mapDomain Sum.inr : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) = γ k :=
  Finsupp.mapDomain_apply_of_injective Sum.inr_injective γ k

theorem mapDomain_inr_inl (γ : Ix m n →₀ ℕ) (k : Ix m n) :
    (γ.mapDomain Sum.inr : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) = 0 :=
  Finsupp.mapDomain_notin_range γ _ (by simp)

theorem k2 (γ : Ix m n →₀ ℕ) : (∀ k ∈ γ.support, inF1 ε k) → ∀ (d : ℕ) (u : Sym m n), SymbolInFirstFamily ε u → EtaLe u d →
    ∃ r, Good ε d r ∧ ∀ g, op u (monomial γ 1 * g) = op (u * monomial (γ.mapDomain Sum.inl) 1) g + op r g := by
  induction γ using Finsupp.induction with
  | zero => intro _ d u _ _; exact ⟨0, good_zero d, fun g => by simp [monomial_zero', op_zero]⟩
  | single_add a b f haf hb ih =>
    intro hsup d u hu hue
    have hsf : ∀ k ∈ f.support, inF1 ε k := by
      intro k hk
      apply hsup k
      have hka : k ≠ a := fun h => haf (h ▸ hk)
      rw [Finsupp.mem_support_iff] at hk ⊢
      simpa [Finsupp.single_apply, Ne.symm hka] using hk
    have hai : inF1 ε a := by
      apply hsup a
      rw [Finsupp.mem_support_iff]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.1 haf, add_zero]
      exact hb
    obtain ⟨r₁, hr₁, e₁⟩ := kpow hai b d u hu hue
    have hu' := first_family_symbol_mul_variable_pow hu hai b
    obtain ⟨r₂, hr₂, e₂⟩ := ih hsf d (u * X (Sum.inl a) ^ b) hu'.1 (hu'.2 d hue)
    obtain ⟨r₃, hr₃, e₃⟩ := ih hsf d r₁ hr₁.1 (good_le hr₁)
    have hM : ∀ k, ((f.mapDomain Sum.inl : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) ≠ 0 ∨
        (f.mapDomain Sum.inl : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k := by
      intro k hk
      rw [mapDomain_inl_inl, mapDomain_inl_inr] at hk
      exact hsf k (Finsupp.mem_support_iff.2 (by tauto))
    have g3 : Good ε d (r₁ * monomial (f.mapDomain Sum.inl) 1) := by
      have := good_mul_monomial (e := 0) hr₁ _ hM (by simp [mapDomain_inl_inr])
      simpa using this
    refine ⟨r₂ + r₁ * monomial (f.mapDomain Sum.inl) 1 + r₃, good_add (good_add hr₂ g3) hr₃, fun g => ?_⟩
    rw [monomial_single_add, mul_assoc, e₁, e₂, e₃, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      monomial_single_add, op_add, op_add]
    have : u * (X (Sum.inl a) ^ b * monomial (Finsupp.mapDomain Sum.inl f) 1) =
        u * X (Sum.inl a) ^ b * monomial (Finsupp.mapDomain Sum.inl f) 1 := by ring
    rw [this]
    ring

theorem op_dvE (w : Sym m n) (δ : Ix m n →₀ ℕ) (f : PX m n) :
    op w (dvE (fun k => δ k) f) = op (w * monomial (δ.mapDomain Sum.inr) 1) f := by
  classical
  conv_rhs => rw [w.as_sum, Finset.sum_mul, op_sum]
  conv_lhs => rw [op]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [monomial_mul, mul_one, op_monomial, opMono_eq, opMono_eq, comapDomain_inl_add]
  have h1 : (δ.mapDomain Sum.inr : Ix m n ⊕ Ix m n →₀ ℕ).comapDomain Sum.inl Sum.inl_injective.injOn = 0 := by
    ext j; simp [Finsupp.comapDomain_apply, mapDomain_inr_inl]
  have h2 : (fun k : Ix m n => (t + δ.mapDomain Sum.inr : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k)) =
      (fun k => t (Sum.inr k)) + fun k => δ k := by
    ext j; simp [mapDomain_inr_inr]
  rw [h1, add_zero, h2, ← dvE_mul]
  rfl

theorem decomp (t : Ix m n ⊕ Ix m n →₀ ℕ) :
    (t.comapDomain Sum.inl Sum.inl_injective.injOn).mapDomain Sum.inl +
      (t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr = t := by
  ext j
  rcases j with j | j
  · simp [mapDomain_inl_inl, mapDomain_inr_inl, Finsupp.comapDomain_apply]
  · simp [mapDomain_inl_inr, mapDomain_inr_inr, Finsupp.comapDomain_apply]

theorem compSt : CompSt := by
  intro m n ε u v d₁ d₂ hu hv hue hve
  classical
  have key : ∀ t ∈ v.support, ∃ r, Good ε (d₁ + d₂) r ∧
      ∀ f, op u (opMono t f) = op (u * monomial t 1) f + op r f := by
    intro t ht
    have hγ : ∀ k ∈ (t.comapDomain Sum.inl Sum.inl_injective.injOn).support, inF1 ε k := by
      intro k hk
      apply hv t ht k
      left
      simpa [Finsupp.comapDomain_apply] using hk
    obtain ⟨r, hr, e⟩ := k2 _ hγ d₁ u hu hue
    have hs : ∀ k, (((t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr : Ix m n ⊕ Ix m n →₀ ℕ)
        (Sum.inl k) ≠ 0 ∨ ((t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr :
          Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k := by
      intro k hk
      rw [mapDomain_inr_inl, mapDomain_inr_inr] at hk
      apply hv t ht k
      right
      simpa [Finsupp.comapDomain_apply] using hk
    have he : (∑ k, ((t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr :
        Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k)) ≤ d₂ := by
      simp only [mapDomain_inr_inr, Finsupp.comapDomain_apply]
      exact hve t ht
    refine ⟨r * monomial ((t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr) 1,
      good_mul_monomial hr _ hs he, fun f => ?_⟩
    rw [opMono_eq, e]
    have hδ : (fun k : Ix m n => t (Sum.inr k)) =
        fun k => (t.comapDomain Sum.inr Sum.inr_injective.injOn) k := by
      ext k; simp [Finsupp.comapDomain_apply]
    rw [hδ, op_dvE, op_dvE, mul_assoc, monomial_mul, mul_one, decomp]
  choose! R hR using key
  refine ⟨∑ t ∈ v.support, AddMonoidAlgebra.coeff v t • R t, ?_, ?_, fun f => ?_⟩
  · exact (good_sum _ _ fun t ht => good_smul _ (hR t ht).1).1
  · exact (good_sum _ _ fun t ht => good_smul _ (hR t ht).1).2
  · rw [show op v f = ∑ t ∈ v.support, AddMonoidAlgebra.coeff v t • opMono t f from rfl, op_sum_f]
    have huv : u * v = ∑ t ∈ v.support, AddMonoidAlgebra.coeff v t • (u * monomial t 1) := by
      conv_lhs => rw [v.as_sum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← mul_smul_comm, smul_monomial, smul_eq_mul, mul_one]
    rw [huv, op_sum, op_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(hR t ht).2, op_smul, op_smul, smul_add]

end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators

theorem PositivityTheory.Rg.Sw.LC.compSt : PositivityTheory.Rg.Sw.LC.CompSt := PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.compSt
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.InvOp

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.LC

theorem invOp : InvOp := B3.invOp_of compSt fftSym

end PositivityTheory.Rg.Sw.LC
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreTop

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.LC

theorem coreLC_of (hF : PositivityTheory.Rg.Sw.FFT) : CoreLC :=
  Core.coreLC_of' bicomm (equivLift_of hF semiFam dens symKComm invOp formFacts) repB formFacts

end PositivityTheory.Rg.Sw.LC
end
end
