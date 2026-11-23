module

public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
public import Development.DiscreteGroups.GlobalIrreducibility.LConvAltA
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.DiscreteGroups.GlobalIrreducibility.LConvAltB

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv

theorem alt_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G) (N : ℕ)
    (hN : UnifAdm G K N) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G →* (H →L[ℂ] H)) (e : H →L[ℂ] H) (hKe' : ∀ κ ∈ K, π κ * e = e) (hee : e * e = e)
    (Y Y' : Submodule ℂ (H →L[ℂ] H))
    (hYs : Y ≤ Submodule.span ℂ (Set.range fun h => π h * e)) (heY : e ∈ Y)
    (hY1 : ∀ h, ∀ y ∈ Y, π h * y ∈ Y) (hYE : ∀ y ∈ Y, e * y ∈ Y)
    (hSm : ∀ y ∈ Y, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u * y = y)
    (hY'Y : Y' ≤ Y) (hY'G : ∀ h, ∀ y ∈ Y', π h * y ∈ Y') (hY'E : ∀ y ∈ Y', e * y ∈ Y') (heY' : e ∉ Y')
    (hmax : ∀ Z : Submodule ℂ (H →L[ℂ] H), Z ≤ Y → (∀ h, ∀ z ∈ Z, π h * z ∈ Z) → e ∉ Z → Y' ≤ Z → Z ≤ Y')
    (d : ℕ) (hd : N ^ 2 < d) (g : Fin d → G) :
    (∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun i => e * π (g (σ i)) * e).prod) * e ∈ Y' := by
  let ρY : Representation ℂ G Y :=
    { toFun := fun h => (LinearMap.mulLeft ℂ (π h)).restrict (fun y hy => hY1 h y hy)
      map_one' := by
        refine LinearMap.ext fun y => Subtype.ext ?_
        show π 1 * (y : H →L[ℂ] H) = y
        rw [map_one, one_mul]
      map_mul' := by
        intro a b
        refine LinearMap.ext fun y => Subtype.ext ?_
        show π (a * b) * (y : H →L[ℂ] H) = π a * (π b * y)
        rw [map_mul, mul_assoc] }
  have hρY : ∀ h (y : Y), ((ρY h y : Y) : H →L[ℂ] H) = π h * y := fun h y => rfl
  let Y'' : Submodule ℂ Y := Y'.comap Y.subtype
  have hρY'' : ∀ h, Y'' ≤ Y''.comap (ρY h) := fun h y hy => hY'G h y hy
  let ρQ : Representation ℂ G (Y ⧸ Y'') :=
    { toFun := fun h => Y''.mapQ Y'' (ρY h) (hρY'' h)
      map_one' := by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        show Submodule.Quotient.mk (ρY 1 y) = Submodule.Quotient.mk y
        rw [map_one]; rfl
      map_mul' := by
        intro a b
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        show Submodule.Quotient.mk (ρY (a * b) y) = Submodule.Quotient.mk (ρY a (ρY b y))
        rw [map_mul]; rfl }
  have hρQ : ∀ h (y : Y), ρQ h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (ρY h y) := fun h y => rfl
  have hsm : IsSmooth ρQ := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective Y'' q
    obtain ⟨U, hUo, hU⟩ := hSm y y.2
    exact alt_isOpen_fix ρQ _ U hUo fun v hv => by
      rw [hρQ]; congr 1; exact Subtype.ext (hU v hv)
  have hmk0 : ∀ y : Y, (Submodule.Quotient.mk y : Y ⧸ Y'') = 0 ↔ (y : H →L[ℂ] H) ∈ Y' :=
    fun y => Submodule.Quotient.mk_eq_zero Y''
  have hirr : ρQ.IsIrreducible := by
    unfold Representation.IsIrreducible
    rw [isSimpleOrder_iff]
    refine ⟨⟨⊥, ⊤, fun hbt => heY' ?_⟩, fun a => ?_⟩
    · have h1 : (Submodule.Quotient.mk (⟨e, heY⟩ : Y) : Y ⧸ Y'') ∈ (⊥ : Subrepresentation ρQ).toSubmodule := by
        rw [hbt]; exact Submodule.mem_top
      exact (hmk0 _).mp ((Submodule.mem_bot ℂ).mp h1)
    · let Z : Submodule ℂ (H →L[ℂ] H) := (a.toSubmodule.comap Y''.mkQ).map Y.subtype
      have hZY : Z ≤ Y := by rintro _ ⟨y, _, rfl⟩; exact y.2
      have hZG : ∀ h, ∀ x ∈ Z, π h * x ∈ Z := by
        rintro h _ ⟨y, hy, rfl⟩
        exact ⟨ρY h y, a.apply_mem_toSubmodule h hy, rfl⟩
      have hY'Z : Y' ≤ Z := by
        intro x hx
        refine ⟨⟨x, hY'Y hx⟩, ?_, rfl⟩
        show Submodule.Quotient.mk _ ∈ a.toSubmodule
        rw [(hmk0 _).mpr hx]
        exact a.toSubmodule.zero_mem
      by_cases heZ : e ∈ Z
      · right
        apply Subrepresentation.toSubmodule_injective
        show a.toSubmodule = ⊤
        refine eq_top_iff.mpr fun q _ => ?_
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective Y'' q
        have hYZ : Y ≤ Z := hYs.trans (Submodule.span_le.mpr (by rintro _ ⟨h, rfl⟩; exact hZG h e heZ))
        obtain ⟨y', hy', hyy⟩ := hYZ y.2
        rw [← Subtype.ext hyy]
        exact hy'
      · left
        apply Subrepresentation.toSubmodule_injective
        show a.toSubmodule = ⊥
        refine eq_bot_iff.mpr fun q hq => ?_
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective Y'' q
        have := hmax Z hZY hZG heZ hY'Z ⟨y, hq, rfl⟩
        exact (Submodule.mem_bot ℂ).mpr ((hmk0 y).mpr this)
  obtain ⟨hfd, hfr⟩ := hN (Y ⧸ Y'') ρQ hsm hirr
  let f : G → (H →L[ℂ] H) := fun h => e * π h * e
  have hfY : ∀ a, ∀ y ∈ Y, f a * y ∈ Y := fun a y hy => by
    show e * π a * e * y ∈ Y
    rw [mul_assoc, mul_assoc]; exact hYE _ (hY1 a _ (hYE y hy))
  let TY : G → Module.End ℂ Y := fun a => (LinearMap.mulLeft ℂ (f a)).restrict (fun y hy => hfY a y hy)
  have hTY'' : ∀ a, Y'' ≤ Y''.comap (TY a) := fun a y hy => by
    show e * π a * e * (y : H →L[ℂ] H) ∈ Y'
    rw [mul_assoc, mul_assoc]; exact hY'E _ (hY'G a _ (hY'E _ hy))
  let T : G → Module.End ℂ (Y ⧸ Y'') := fun a => Y''.mapQ Y'' (TY a) (hTY'' a)
  have hfixmk : ∀ y : Y, e * (y : H →L[ℂ] H) = y → Submodule.Quotient.mk y ∈ fixed ρQ K := by
    intro y hy
    show ∀ κ : K, _
    intro κ
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [hρQ]; congr 1; apply Subtype.ext
    rw [hρY, ← hy, ← mul_assoc, hKe' κ κ.2]
  have hTW : ∀ a q, T a q ∈ fixed ρQ K := by
    intro a q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective Y'' q
    exact hfixmk (TY a y) (by show e * (e * π a * e * (y : H →L[ℂ] H)) = e * π a * e * y; simp only [← mul_assoc, hee])
  have := hfd
  let t : G → Module.End ℂ (fixed ρQ K) := fun a => (T a).restrict (fun q _ => hTW a q)
  have hdim : Module.finrank ℂ (Module.End ℂ (fixed ρQ K)) < d := by
    rw [Module.finrank_linearMap, ← sq]
    exact lt_of_le_of_lt (Nat.pow_le_pow_left hfr 2) hd
  have h0 := alt_std_eq_zero hdim fun i => t (g i)
  have key : ∀ (l : List G) (w : fixed ρQ K), (((l.map t).prod w : fixed ρQ K) : Y ⧸ Y'') = (l.map T).prod w := by
    intro l w
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      exact congrArg (T a) ih
  have key2 : ∀ (l : List G) (y : Y),
      (l.map T).prod (Submodule.Quotient.mk y) = Submodule.Quotient.mk ((l.map TY).prod y) := by
    intro l y
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]; rfl
  have key3 : ∀ (l : List G) (y : Y), (((l.map TY).prod y : Y) : H →L[ℂ] H) = (l.map f).prod * y := by
    intro l y
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.map_cons, List.prod_cons, mul_assoc, ← ih]
      rfl
  let e' : Y := ⟨e, heY⟩
  have he'W : Submodule.Quotient.mk e' ∈ fixed ρQ K := hfixmk e' hee
  have h1 := congrArg (fun X : Module.End ℂ (fixed ρQ K) => ((X ⟨_, he'W⟩ : fixed ρQ K) : Y ⧸ Y'')) h0
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    LinearMap.zero_apply, ZeroMemClass.coe_zero] at h1
  have hsum : ∀ σ : Equiv.Perm (Fin d), (((List.ofFn fun i => t (g (σ i))).prod ⟨_, he'W⟩ : fixed ρQ K) : Y ⧸ Y'')
      = Y''.mkQ (((List.ofFn fun i => g (σ i)).map TY).prod e') := by
    intro σ
    rw [show (List.ofFn fun i => t (g (σ i))) = (List.ofFn fun i => g (σ i)).map t by rw [List.map_ofFn]; rfl,
      key, key2]
    rfl
  have h1' : Y''.mkQ (∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((List.ofFn fun i => g (σ i)).map TY).prod e') = 0 := by

    rw [map_sum]
    refine (Finset.sum_congr rfl fun σ _ => ?_).trans h1
    rw [map_smul, hsum]
  have h2 := (Submodule.Quotient.mk_eq_zero Y'').mp h1'
  have h3 : ((∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((List.ofFn fun i => g (σ i)).map TY).prod e' : Y) : H →L[ℂ] H) =
      (∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun i => e * π (g (σ i)) * e).prod) * e := by
    rw [Submodule.coe_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Submodule.coe_smul, key3, smul_mul_assoc,
      show (List.ofFn fun i => e * π (g (σ i)) * e) = (List.ofFn fun i => g (σ i)).map f by rw [List.map_ofFn]; rfl]
  rw [← h3]
  exact h2

end DiscreteGroups.sglob.LConv
end
end
end

-- Source module: Development.DiscreteGroups.GlobalIrreducibility.LConv

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv

theorem altIdentity : AltIdentity := by
  intro G _ _ _ K hKo hKc _ N hN H _ _ _ π hπ e he hKe hfix d hd g
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0] at hd
    exact Nat.not_lt_zero _ hd
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hd0
  have hstar : ∀ a, star (π a) = π a⁻¹ := alt_star_eq π hπ
  have hes : star e = e := he.star_eq
  have hKe' : ∀ κ ∈ K, π κ * e = e := fun κ hκ => ContinuousLinearMap.ext fun x => hKe x κ hκ
  have hee : e * e = e := ContinuousLinearMap.ext fun x => hfix (e x) fun κ hκ => hKe x κ hκ
  have heK : ∀ κ ∈ K, e * π κ = e := by
    intro κ hκ
    have h1 := hKe' κ⁻¹ (K.inv_mem hκ)
    calc e * π κ = star (π κ⁻¹ * e) := by rw [star_mul, hes, hstar, inv_inv]
      _ = e := by rw [h1, hes]
  let f : G → (H →L[ℂ] H) := fun a => e * π a * e
  let Y : Submodule ℂ (H →L[ℂ] H) := Submodule.span ℂ (Set.range fun a => π a * e)
  have hY1 : ∀ a, ∀ y ∈ Y, π a * y ∈ Y := by
    intro a y hy
    have : Y ≤ Y.comap (LinearMap.mulLeft ℂ (π a)) := Submodule.span_le.mpr (by
      rintro _ ⟨b, rfl⟩
      show π a * (π b * e) ∈ Y
      exact Submodule.subset_span ⟨a * b, by simp only [map_mul, mul_assoc]⟩)
    exact this hy
  have hSm : ∀ y ∈ Y, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u * y = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨K.comap (MulAut.conj a⁻¹).toMonoidHom, ?_, fun u hu => ?_⟩
      · have : ((K.comap (MulAut.conj a⁻¹).toMonoidHom : Subgroup G) : Set G) =
            (fun h => a⁻¹ * h * a) ⁻¹' (K : Set G) := by
          ext h; simp
        rw [this]
        exact hKo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
      · have hu' : a⁻¹ * u * a ∈ K := by simpa [MulAut.conj_apply] using hu
        calc π u * (π a * e) = π (u * a) * e := by rw [map_mul, mul_assoc]
          _ = π (a * (a⁻¹ * u * a)) * e := by rw [show a * (a⁻¹ * u * a) = u * a by group]
          _ = π a * (π (a⁻¹ * u * a) * e) := by rw [map_mul, mul_assoc]
          _ = π a * e := by rw [hKe' _ hu']
    | zero => exact ⟨⊤, by simp, fun u _ => by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨U₁, h1o, h1⟩ := hx
      obtain ⟨U₂, h2o, h2⟩ := hz
      refine ⟨U₁ ⊓ U₂, by rw [Subgroup.coe_inf]; exact h1o.inter h2o, fun u hu => ?_⟩
      rw [mul_add, h1 u hu.1, h2 u hu.2]
    | smul c x _ hx =>
      obtain ⟨U, ho, h⟩ := hx
      exact ⟨U, ho, fun u hu => by rw [mul_smul_comm, h u hu]⟩
  have hYe : ∀ y ∈ Y, y * e = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; simp only [mul_assoc, hee]
    | zero => simp
    | add x z _ _ hx hz => rw [add_mul, hx, hz]
    | smul c x _ hx => rw [smul_mul_assoc, hx]
  have heY : e ∈ Y := Submodule.subset_span ⟨1, by simp⟩
  have hE : ∀ Z : Submodule ℂ (H →L[ℂ] H), Z ≤ Y → (∀ a, ∀ z ∈ Z, π a * z ∈ Z) → ∀ z ∈ Z, e * z ∈ Z := by
    intro Z hZY hZ z hz
    obtain ⟨U, hUo, hU⟩ := hSm z (hZY hz)
    exact alt_avg K hKc π e heK hfix Z (fun κ _ => hZ κ) z hz U hUo hU
  have hYE : ∀ y ∈ Y, e * y ∈ Y := hE Y le_rfl hY1
  have hYmul : ∀ x ∈ Y, ∀ y ∈ Y, x * y ∈ Y := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      show π a * e * y ∈ Y
      rw [mul_assoc]; exact hY1 a _ (hYE y hy)
    | zero => simp
    | add x z _ _ hx hz => rw [add_mul]; exact Y.add_mem hx hz
    | smul c x _ hx => rw [smul_mul_assoc]; exact Y.smul_mem c hx
  have hword : ∀ Z : Submodule ℂ (H →L[ℂ] H), Z ≤ Y → (∀ a, ∀ z ∈ Z, π a * z ∈ Z) →
      ∀ l : List G, ∀ z ∈ Z, (l.map f).prod * z ∈ Z := by
    intro Z hZY hZ l
    induction l with
    | nil => intro z hz; simpa using hz
    | cons a l ih =>
      intro z hz
      rw [List.map_cons, List.prod_cons, mul_assoc]
      show e * π a * e * ((l.map f).prod * z) ∈ Z
      rw [mul_assoc, mul_assoc]
      exact hE Z hZY hZ _ (hZ a _ (hE Z hZY hZ _ (ih z hz)))
  have hfstar : ∀ a, star (f a) = f a⁻¹ := by
    intro a
    show star (e * π a * e) = e * π a⁻¹ * e
    simp only [star_mul, hes, hstar, mul_assoc]
  have hwstar : ∀ l : List G, star ((l.map f).prod) = ((l.reverse.map (·⁻¹)).map f).prod := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp [List.reverse_cons, List.map_append, List.prod_append, star_mul, ih, hfstar]
  have hterm : ∀ σ : Equiv.Perm (Fin (n + 1)),
      (List.ofFn fun i => e * π (g (σ i)) * e) = (List.ofFn fun i => g (σ i)).map f := by
    intro σ; rw [List.map_ofFn]; rfl
  set S := ∑ σ : Equiv.Perm (Fin (n + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
    (List.ofFn fun i => e * π (g (σ i)) * e).prod with hSdef
  have hSZ : ∀ Z : Submodule ℂ (H →L[ℂ] H), Z ≤ Y → (∀ a, ∀ z ∈ Z, π a * z ∈ Z) →
      ∀ z ∈ Z, S * z ∈ Z ∧ star S * z ∈ Z := by
    intro Z hZY hZ z hz
    constructor
    · rw [hSdef, Finset.sum_mul]
      refine Z.sum_mem fun σ _ => ?_
      rw [smul_mul_assoc, hterm]
      exact Z.smul_mem _ (hword Z hZY hZ _ z hz)
    · rw [hSdef, star_sum, Finset.sum_mul]
      refine Z.sum_mem fun σ _ => ?_
      rw [star_smul, star_intCast, hterm, hwstar, smul_mul_assoc]
      exact Z.smul_mem _ (hword Z hZY hZ _ z hz)
  have hQ : ∀ (l : List G) a, f a * (l.map f).prod * e = f a * (l.map f).prod := by
    intro l
    induction l with
    | nil =>
      intro a
      simp only [List.map_nil, List.prod_nil, mul_one]
      show e * π a * e * e = e * π a * e
      rw [mul_assoc, hee]
    | cons b l ih => intro a; rw [List.map_cons, List.prod_cons, mul_assoc (f a), ih b]
  have hSe : S * e = S := by
    rw [hSdef, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_mul_assoc, hterm, List.ofFn_succ, List.map_cons, List.prod_cons, hQ]
  have heSs : e * star S = star S := by
    have := congrArg star hSe
    rwa [star_mul, hes] at this
  have hSY : S ∈ Y := by rw [← hSe]; exact (hSZ Y le_rfl hY1 e heY).1
  by_contra hS
  have : Nontrivial (H →L[ℂ] H) := nontrivial_of_ne S 0 hS
  set c := star S * S with hc
  have hcsa : IsSelfAdjoint c := IsSelfAdjoint.star_mul_self S
  have hc0 : c ≠ 0 := by
    intro h0
    have : ‖S‖ * ‖S‖ = 0 := by rw [← CStarRing.norm_star_mul_self, ← hc, h0, norm_zero]
    exact hS (norm_eq_zero.mp (mul_self_eq_zero.mp this))
  have hec : e * c = c := by rw [hc, ← mul_assoc, heSs]
  have hcY : c ∈ Y := (hSZ Y le_rfl hY1 S hSY).2
  obtain ⟨z, hz, hzn⟩ := spectrum.exists_nnnorm_eq_spectralRadius c
  rw [hcsa.spectralRadius_eq_nnnorm] at hzn
  have hz0 : z ≠ 0 := by
    intro h0
    apply hc0
    rw [h0, enorm_zero, eq_comm, ENNReal.coe_eq_zero, nnnorm_eq_zero] at hzn
    exact hzn
  have hzr : star z = z := by
    rw [hcsa.mem_spectrum_eq_re hz]
    exact Complex.conj_ofReal _
  have hnotl : ∀ y ∈ Y, y * (c - z • e) ≠ e := by
    intro y hy hyu
    set b := e * y with hb
    have hbe : b * e = b := by rw [hb, mul_assoc, hYe y hy]
    have hbu : b * (c - z • e) = e := by rw [hb, mul_assoc, hyu, hee]
    have h1 : b * (c - z • (1 : H →L[ℂ] H)) = e := by
      calc b * (c - z • (1 : H →L[ℂ] H)) = b * c - z • b := by rw [mul_sub, mul_smul_comm, mul_one]
        _ = b * c - z • (b * e) := by rw [hbe]
        _ = b * (c - z • e) := by rw [mul_sub, mul_smul_comm]
        _ = e := hbu
    have h2 : (1 - e) * (c - z • (1 : H →L[ℂ] H)) = -(z • (1 - e)) := by
      rw [sub_mul, one_mul, mul_sub, hec, mul_smul_comm, mul_one, smul_sub]
      abel
    have hL : (b - z⁻¹ • (1 - e)) * (c - z • (1 : H →L[ℂ] H)) = 1 := by
      rw [sub_mul, h1, smul_mul_assoc, h2, smul_neg, smul_smul, inv_mul_cancel₀ hz0, one_smul]
      abel
    set L := b - z⁻¹ • (1 - e) with hLd
    have hv : star (c - z • (1 : H →L[ℂ] H)) = c - z • 1 := by
      rw [star_sub, hcsa.star_eq, star_smul, hzr, star_one]
    have hR : (c - z • (1 : H →L[ℂ] H)) * star L = 1 := by
      have := congrArg star hL
      rwa [star_mul, hv, star_one] at this
    have hLR : L = star L := by
      calc L = L * ((c - z • (1 : H →L[ℂ] H)) * star L) := by rw [hR, mul_one]
        _ = star L := by rw [← mul_assoc, hL, one_mul]
    have hunit : IsUnit (c - z • (1 : H →L[ℂ] H)) := ⟨⟨c - z • 1, L, by rw [hLR]; exact hR, hL⟩, rfl⟩
    apply spectrum.mem_iff.mp hz
    rw [Algebra.algebraMap_eq_smul_one, ← neg_sub]
    exact hunit.neg
  let s : Set (Submodule ℂ (H →L[ℂ] H)) := {Z | Z ≤ Y ∧ (∀ a, ∀ x ∈ Z, π a * x ∈ Z) ∧ e ∉ Z}
  have hZ0 : Y.map (LinearMap.mulRight ℂ (c - z • e)) ∈ s := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      show y * (c - z • e) ∈ Y
      rw [mul_sub, mul_smul_comm, hYe y hy]
      exact Y.sub_mem (hYmul y hy c hcY) (Y.smul_mem z hy)
    · rintro a _ ⟨y, hy, rfl⟩
      exact ⟨π a * y, hY1 a y hy, by simp [mul_assoc]⟩
    · rintro ⟨y, hy, hyu⟩
      exact hnotl y hy hyu
  obtain ⟨Y', hZY', hmax⟩ := zorn_le_nonempty₀ s (by
    intro C hCs hC Z0 hZ0C
    refine ⟨sSup C, ⟨sSup_le fun Z hZ => (hCs hZ).1, ?_, ?_⟩, fun Z hZ => le_sSup hZ⟩
    · intro a x hx
      obtain ⟨Z, hZ, hxZ⟩ := (Submodule.mem_sSup_of_directed ⟨Z0, hZ0C⟩ hC.directedOn).mp hx
      exact le_sSup hZ ((hCs hZ).2.1 a x hxZ)
    · intro he'
      obtain ⟨Z, hZ, hxZ⟩ := (Submodule.mem_sSup_of_directed ⟨Z0, hZ0C⟩ hC.directedOn).mp he'
      exact (hCs hZ).2.2 hxZ) _ hZ0
  obtain ⟨hY'Y, hY'G, heY'⟩ := hmax.prop
  have hY'E : ∀ x ∈ Y', e * x ∈ Y' := hE Y' hY'Y hY'G
  have hq := alt_quot K N hN π e hKe' hee Y Y' le_rfl heY hY1 hYE hSm hY'Y hY'G hY'E heY'
    (fun Z hZY hZG heZ hle => hmax.le_of_ge ⟨hZY, hZG, heZ⟩ hle) (n + 1) hd g
  rw [← hSdef, hSe] at hq
  have hcY' : c ∈ Y' := (hSZ Y' hY'Y hY'G S hq).2
  have huY' : c - z • e ∈ Y' := by
    have h := hZY' ⟨e, heY, rfl⟩
    have h' : (LinearMap.mulRight ℂ (c - z • e)) e = c - z • e := by
      rw [LinearMap.mulRight_apply, mul_sub, hec, mul_smul_comm, hee]
    rwa [h'] at h
  have hze : z • e ∈ Y' := by
    have := Y'.sub_mem hcY' huY'
    rwa [sub_sub_cancel] at this
  apply heY'
  have := Y'.smul_mem z⁻¹ hze
  rwa [smul_smul, inv_mul_cancel₀ hz0, one_smul] at this

end DiscreteGroups.sglob.LConv
end
end
end
