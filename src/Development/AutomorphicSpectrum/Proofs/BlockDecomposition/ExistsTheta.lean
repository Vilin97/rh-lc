module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartBaseChangeMapUniqueStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolyEqPolyEquiv
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartExtendBaseChangeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartFormsBaseChangeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSingletonBaseChangeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFormsMapInjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsetSystemInjectiveExtensionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsetSystemScalarTowerExtStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialFormInRelativeImageStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialFormsBasisStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeFormsMapMemSpanStatement
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartEmptyBaseChange

section

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem toR_empty_bijective {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A]
    (C : ChartRings K A n d) : Function.Bijective (toR C ∅) := by
  have h : (toR C ∅ : A → C.R ∅) = C.base.symm := funext fun a => C.res_id ∅ _ _
  rw [h]
  exact C.base.symm.bijective

theorem theta_empty : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d),
    ∃ (θ : R0 K n d ∅ →ₐ[K] C.R ∅) (hθ : ∀ b, θ (poly n K ∅ b) = toR C ∅ (phi C b)),
      IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  intro K _ n d A _ _ C
  let e : Bp K n d ≃ₐ[K] R0 K n d ∅ := AlgEquiv.ofBijective (poly n K ∅) PolyBij.poly_bijective
  let θ : R0 K n d ∅ →ₐ[K] C.R ∅ := (toR C ∅).comp ((phi C).comp e.symm.toAlgHom)
  have hθ : ∀ b, θ (poly n K ∅ b) = toR C ∅ (phi C b) := fun b => by
    have hb : e.symm (poly n K ∅ b) = b := e.symm_apply_apply b
    change toR C ∅ (phi C (e.symm (poly n K ∅ b))) = _
    rw [hb]
  refine ⟨θ, hθ, ?_⟩
  let eM : Bp K n d ≃ₗ[Bp K n d] R0 K n d ∅ :=
    LinearEquiv.ofBijective (Algebra.linearMap (Bp K n d) (R0 K n d ∅)) PolyBij.poly_bijective
  let eN : Aa C ≃ₗ[Aa C] Rb C ∅ :=
    LinearEquiv.ofBijective (Algebra.linearMap (Aa C) (Rb C ∅)) (toR_empty_bijective C)
  refine (IsBaseChange.iff_of_equiv_comm (f := Algebra.linearMap (Bp K n d) (Aa C)) eM eN ?_).mp
    (IsBaseChange.linearMap (Bp K n d) (Aa C))
  refine LinearMap.ext fun b => ?_
  exact hθ b

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartEmptyBaseChangeStatement

section

@[expose] public section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.chart_empty_base_change : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d), ∃ (θ : R0 K n d ∅ →ₐ[K] C.R ∅) (hθ : ∀ b, θ (poly n K ∅ b) = toR C ∅ (phi C b)), IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty.theta_empty | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty.theta_empty | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty.theta_empty <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExPOfCompatibleEquiv

section

@[expose] public section

set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto

theorem dZ_addEquiv_apply {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T)
    (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) (m : ℕ)
    (c : ∀ i : Fin (m + 1) → ι, M (ent i)) (i : Fin (m + 2) → ι) :
    e _ (dZ M r m c i) = dZ N r' m (fun i => e _ (c i)) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dZ, map_sum, map_zsmul, hn]

theorem dZ_eq_zero_of_addEquiv {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T)
    (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) (m : ℕ)
    (c : ∀ i : Fin (m + 1) → ι, N (ent i)) (hc : dZ N r' m c = 0) :
    dZ M r m (fun i => (e _).symm (c i)) = 0 := by
  funext i
  apply (e _).injective
  rw [dZ_addEquiv_apply M N r r' e hn m, Pi.zero_apply, map_zero]
  simp only [AddEquiv.apply_symm_apply]
  exact congrFun hc i

theorem exP_of_addEquiv : ∀ {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T) (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S), (∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) → ExP M r → ExP N r' := by
  intro ι _ M N _ _ r r' e hn hM
  obtain ⟨h0, h1, h2⟩ := hM
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx' : (e ∅).symm x = 0 := by
      apply h0
      intro i
      have h7 := hn (Finset.empty_subset (ent i)) ((e ∅).symm x)
      rw [AddEquiv.apply_symm_apply] at h7
      have h8 : r' (Finset.empty_subset (ent i)) x = 0 := hx i
      rw [h8] at h7
      exact (e _).injective (h7.trans (map_zero _).symm)
    simpa using congrArg (e ∅) hx'
  · intro c hc
    obtain ⟨x, hx⟩ := h1 (fun i => (e _).symm (c i)) (dZ_eq_zero_of_addEquiv M N r r' e hn 0 c hc)
    refine ⟨e ∅ x, fun i => ?_⟩
    have h5 : r (Finset.empty_subset (ent i)) x = (e _).symm (c i) := hx i
    have h6 := hn (Finset.empty_subset (ent i)) x
    rw [h5, AddEquiv.apply_symm_apply] at h6
    exact h6.symm
  · intro m c hc
    obtain ⟨b, hb⟩ := h2 m (fun i => (e _).symm (c i)) (dZ_eq_zero_of_addEquiv M N r r' e hn (m + 1) c hc)
    refine ⟨fun i => e _ (b i), ?_⟩
    funext i
    have h3 := dZ_addEquiv_apply M N r r' e hn m b i
    have h4 : dZ M r m b i = (e _).symm (c i) := congrFun hb i
    rw [h4, AddEquiv.apply_symm_apply] at h3
    exact h3.symm

end GlobalTheory.CompanionTheory.SurjectionOntoH4
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExPOfCompatibleEquivStatement

section

@[expose] public section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.exP_of_compatible_equiv : ∀ {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T) (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S), (∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) → ExP M r → ExP N r' := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.exP_of_addEquiv | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.exP_of_addEquiv | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.exP_of_addEquiv <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PmExactnessOfExP

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι]

theorem cech_d_eq_dZ (P : PM.{0} R ι) (n : ℕ) (c : P.cech.X n) :
    P.cech.d n c = dZ P.M (fun h x => P.res h x) n c := by
  funext i
  simp only [CrystallineSemistableComparison.Cos.d, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, dZ]
  rfl

theorem cech_d_aug (P : PM.{0} R ι) (x : P.M ∅) : P.cech.d 0 (P.aug x) = 0 := by
  rw [cech_d_eq_dZ]
  funext i
  have key : ∀ (k : Fin 2), P.res (ent_comp i k.succAbove) (P.aug x (i ∘ k.succAbove)) =
      P.res (Finset.empty_subset (ent i)) x := fun k => P.res_comp _ _ x
  simp only [dZ, Fin.sum_univ_two, key]
  simp
  rfl

theorem ex_of_exP : ∀ {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] (P : PM.{0} R ι),
    ExP P.M (fun h x => P.res h x) → P.Ex := by
  intro R _ ι _ P h
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨cech_d_aug P, fun x hx => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · rw [one_smul]
    exact h0 x fun i => congrFun hx i
  · obtain ⟨x, hx⟩ := h1 y ((cech_d_eq_dZ P 0 y).symm.trans hy)
    exact ⟨x, (funext hx).trans (one_smul _ _).symm⟩
  · obtain ⟨b, hb⟩ := h2 n y ((cech_d_eq_dZ P (n + 1) y).symm.trans hy)
    exact ⟨b, ((cech_d_eq_dZ P n b).trans hb).trans (one_smul _ _).symm⟩

end GlobalTheory.CompanionTheory.SurjectionOntoH4
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PmExactnessOfExPStatement

section

@[expose] public section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.pm_exactness_of_exP : ∀ {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] (P : PM.{0} R ι), ExP P.M (fun h x => P.res h x) → P.Ex := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ex_of_exP | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ex_of_exP | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ex_of_exP <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTheta

section

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto

variable {K : Type} [Field K] {n d : ℕ}

theorem exists_theta {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) :
    ∃ (θ : ∀ S, R0 K n d S →ₐ[K] C.R S) (hθ : ∀ S b, θ S (poly n K S b) = toR C S (phi C b)),
      (∀ {S T : Finset (Fin d)} (h : S ⊆ T) y, C.res h (θ S y) = θ T (incl (cone_mono h) y)) ∧
      ∀ S, IsBaseChange (Aa C) (thetaLin C (θ S) (hθ S)) := by
  have key : ∀ S, ∃ (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b)),
      IsBaseChange (Aa C) (thetaLin C θ hθ) := by
    intro S
    rcases S.eq_empty_or_nonempty with rfl | ⟨k, hk⟩
    · exact GlobalTheory.T.chart_empty_base_change C
    · obtain ⟨θ₁, h₁, hu, hb⟩ := GlobalTheory.T.chart_singleton_base_change C k
      exact GlobalTheory.T.chart_extend_base_change C S k hk θ₁ h₁ hu hb
  choose θ hθ bc using key
  refine ⟨θ, hθ, ?_, bc⟩
  intro S T h y
  have := GlobalTheory.T.chart_base_change_map_unique C ((C.res h).comp (θ S)) ((θ T).comp (incl (cone_mono h)))
    (fun b => by rw [AlgHom.comp_apply, hθ, res_toR]) (fun b => by rw [AlgHom.comp_apply, incl_poly h, hθ]) (θ T) (hθ T) (bc T)
  exact DFunLike.congr_fun this y

theorem Tset_ne_univ (g : Gam n d) (D : Finset (E n d)) (h : good g D) : Tset g D ≠ Finset.univ := by
  intro hu
  have hneg : ∀ j, g (Sum.inr j) ≤ 0 := fun j => by
    have : j ∈ Tset g D := hu ▸ Finset.mem_univ j
    rcases (Finset.mem_filter.1 this).2 with h | h
    · exact h.le
    · exact h.1.le
  have : tdeg g ≤ 0 := Finset.sum_nonpos fun j _ => hneg j
  have := h.2
  omega

theorem model_ex (a : ℕ) : ExP (fun S : Finset (Fin d) => relOm K (I0 n K S) a)
    (fun {S T} h => relMap (incl (cone_mono h)) (cone_ideal_map_mono (S := S) (T := T) h) a) := by
  obtain ⟨b, hb⟩ := GlobalTheory.T.monomial_forms_basis (K := K) (n := n) (d := d) a
  refine GlobalTheory.T.finset_system_injective_extension (K := K) b (fun p => good p.1 p.2.1) (fun p => Tset p.1 p.2.1) (fun p h => Tset_ne_univ _ _ h) _ _
    (fun S => ((omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a).toAddMonoidHom).comp
      (relOm K (I0 n K S) a).subtype.toAddMonoidHom) ?_ ?_ ?_
  · intro S x y hxy
    exact Subtype.ext (GlobalTheory.T.cone_forms_map_injective S a hxy)
  · intro S S' h x
    change omMap _ a (omMap _ a (x : Om K (R0 K n d S) a)) = omMap _ a (x : Om K (R0 K n d S) a)
    rw [omMap_comp, incl_comp]
  · intro S w
    have hset : (b '' {l | good l.1 l.2.1 ∧ Tset l.1 l.2.1 ⊆ S}) =
        {w | ∃ (g : Gam n d) (D : {D : Finset (E n d) // D.card = a}), good g D.1 ∧ Tset g D.1 ⊆ S ∧ w = monW K g D} := by
      ext w
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.1, p.2, hp.1, hp.2, hb p⟩
      · rintro ⟨g, D, h1, h2, rfl⟩
        exact ⟨(g, D), ⟨h1, h2⟩, hb _⟩
    rw [hset]
    constructor
    · rintro ⟨x, rfl⟩
      exact GlobalTheory.T.relative_forms_map_mem_span S a _ x.2
    · intro hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨g, D, h1, h2, rfl⟩ := hw
        obtain ⟨ω, hω, e⟩ := GlobalTheory.T.monomial_form_in_relative_image (K := K) S a g D h1 h2
        exact ⟨⟨ω, hω⟩, e⟩
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        exact ⟨x' + y', map_add _ _ _⟩
      | smul c x _ hx =>
        obtain ⟨x', rfl⟩ := hx
        exact ⟨c • x', map_smul (omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a) c _⟩

theorem h4a : ChartFormsCechExact := by
  intro K _ _ A _ _ n d hd C a P e he
  obtain ⟨θ, hθ, nat, bc⟩ := exists_theta C
  haveI := etale_Aa C
  have h1 := model_ex (K := K) (n := n) (d := d) a
  have h2 : ExP (fun S => relA C S a) (fun {S T} h => relMap (C.res h) (res_mem_I C (S := S) (T := T) h) a) := by
    refine GlobalTheory.T.finset_system_scalar_tower_ext (B := Bp K n d) (A := Aa C) (fun S => relOm K (I0 n K S) a) (fun S => relA C S a) _ ?_ _ ?_
      (fun S => psi C (θ S) (hθ S) a) (fun S => GlobalTheory.T.chart_forms_base_change C (θ S) (hθ S) (bc S) a) ?_ h1
    · intro S T h
      refine ⟨map_add _, fun b ω => Subtype.ext ?_⟩
      change omMap (incl (cone_mono h)) a ((b • ω : relOm K (I0 n K S) a) : Om K (R0 K n d S) a) =
        ((b • relMap (incl (cone_mono h)) (cone_ideal_map_mono h) a ω : relOm K (I0 n K T) a) : Om K (R0 K n d T) a)
      have e1 : ∀ (U : Finset (Fin d)) (ω' : relOm K (I0 n K U) a), ((b • ω' : relOm K (I0 n K U) a) : Om K (R0 K n d U) a) =
          poly n K U b • (ω' : Om K (R0 K n d U) a) := fun U ω' =>
        (algebraMap_smul (R0 K n d U) b (ω' : Om K (R0 K n d U) a)).symm
      rw [e1, e1, omMap_smul, incl_poly h]
      rfl
    · intro S T h
      refine ⟨map_add _, fun c y => Subtype.ext ?_⟩
      change omMap (C.res h) a (toR C S c • (y : relOm K (C.I S) a).1) = toR C T c • omMap (C.res h) a (y : relOm K (C.I S) a).1
      rw [omMap_smul]
      exact congrArg (· • omMap (C.res h) a (y : relOm K (C.I S) a).1) (res_toR C h c)
    · intro S T h ω
      refine Subtype.ext ?_
      change omMap (C.res h) a (omMap (θ S) a (ω : Om K (R0 K n d S) a)) =
        omMap (θ T) a (omMap (incl (cone_mono h)) a (ω : Om K (R0 K n d S) a))
      have e2 : (C.res h).comp (θ S) = (θ T).comp (incl (cone_mono h)) := AlgHom.ext fun y => nat h y
      rw [omMap_comp, omMap_comp, e2]
  refine GlobalTheory.T.pm_exactness_of_exP P (GlobalTheory.T.exP_of_compatible_equiv _ _ (fun {S T} h => relMap (C.res h) (res_mem_I C (S := S) (T := T) h) a) _
    (fun S => ((e S).symm.toAddEquiv : relA C S a ≃+ P.M S)) ?_ h2)
  intro S T h x
  apply (e T).injective
  refine Subtype.ext ?_
  have := he h ((e S).symm x)
  simp only [LinearEquiv.apply_symm_apply] at this
  have h3 := LinearEquiv.apply_symm_apply (e T) (relMap (C.res h) (res_mem_I C h) a x)
  exact (congrArg Subtype.val h3).trans this.symm

end GlobalTheory.CompanionTheory.SurjectionOntoH4
end
end
end
