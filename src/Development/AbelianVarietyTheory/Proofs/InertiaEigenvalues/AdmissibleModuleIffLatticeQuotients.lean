module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TotallySplit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AutCongrContinuousCycInertia
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSSRepMapOfAbsIrrDistinct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BrauerNesbittSemisimpleMatrixRepresentationsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthOfFiniteDimensional
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
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
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
import Mathlib.Topology.Order.Hom.Esakia
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSSModRepLatRepIff

section

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

noncomputable section
namespace GlobalTheory.RedCharpoly

section Transfer
variable {A B M M₁ : Type} [Ring A] [Ring B] [AddCommGroup M] [Module A M] [AddCommGroup M₁] [Module B M₁]

def subIso (e : M ≃+ M₁) (h1 : ∀ a : A, ∃ b : B, ∀ x, e (a • x) = b • e x)
    (h2 : ∀ b : B, ∃ a : A, ∀ x, e (a • x) = b • e x) : Submodule A M ≃o Submodule B M₁ where
  toFun p :=
    { carrier := {y | e.symm y ∈ p}
      add_mem' := fun {x y} hx hy => by
        change e.symm (x + y) ∈ p
        rw [map_add (f := _)]; exact p.add_mem hx hy
      zero_mem' := by
        change e.symm 0 ∈ p
        rw [map_zero]; exact p.zero_mem
      smul_mem' := fun b y hy => by
        obtain ⟨a, ha⟩ := h2 b
        change e.symm (b • y) ∈ p
        have : e.symm (b • y) = a • e.symm y := by
          rw [AddEquiv.symm_apply_eq, ha, AddEquiv.apply_symm_apply]
        rw [this]; exact p.smul_mem a hy }
  invFun q :=
    { carrier := {x | e x ∈ q}
      add_mem' := fun {x y} hx hy => by
        change e (x + y) ∈ q
        rw [map_add (f := _)]; exact q.add_mem hx hy
      zero_mem' := by
        change e 0 ∈ q
        rw [map_zero]; exact q.zero_mem
      smul_mem' := fun a x hx => by
        obtain ⟨b, hb⟩ := h1 a
        change e (a • x) ∈ q
        rw [hb]; exact q.smul_mem b hx }
  left_inv p := by
    ext x
    change e.symm (e x) ∈ p ↔ _
    rw [AddEquiv.symm_apply_apply]
  right_inv q := by
    ext y
    change e (e.symm y) ∈ q ↔ _
    rw [AddEquiv.apply_symm_apply]
  map_rel_iff' {p p'} := by
    constructor
    · intro h x hx
      have : e.symm (e x) ∈ p' := h (show e.symm (e x) ∈ p by rwa [AddEquiv.symm_apply_apply])
      rwa [AddEquiv.symm_apply_apply] at this
    · intro h y hy
      exact h hy

theorem exists_subquot (e : M ≃+ M₁) (p q : Submodule A M) (p₁ q₁ : Submodule B M₁)
    (hp : ∀ y, y ∈ p₁ ↔ e.symm y ∈ p) (hq : ∀ y, y ∈ q₁ ↔ e.symm y ∈ q) :
    ∃ f : (↥p ⧸ q.comap p.subtype) ≃+ (↥p₁ ⧸ q₁.comap p₁.subtype),
      ∀ (a : A) (b : B), (∀ x, e (a • x) = b • e x) → ∀ z, f (a • z) = b • f z := by
  let e' : ↥p ≃+ ↥p₁ :=
    { toFun := fun x => ⟨e x, (hp _).2 (by simp)⟩
      invFun := fun y => ⟨e.symm y, (hp _).1 y.2⟩
      left_inv := fun x => by simp
      right_inv := fun y => by simp
      map_add' := fun x y => by simp }
  refine ⟨QuotientAddGroup.congr (q.comap p.subtype).toAddSubgroup (q₁.comap p₁.subtype).toAddSubgroup e' ?_,
    fun a b hab z => ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change e x ∈ q₁
      rw [hq, AddEquiv.symm_apply_apply]
      exact hx
    · intro hy
      exact ⟨e'.symm y, (hq _).1 hy, e'.apply_symm_apply y⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    change Submodule.Quotient.mk (e' (a • x)) = Submodule.Quotient.mk (b • e' x)
    congr 1
    exact Subtype.ext (hab x)

variable {N N₁ : Type} [AddCommGroup N] [Module A N] [AddCommGroup N₁] [Module B N₁]

theorem sameFactors_transfer (e : M ≃+ M₁) (e' : N ≃+ N₁)
    (h1 : ∀ a : A, ∃ b : B, (∀ x, e (a • x) = b • e x) ∧ ∀ x, e' (a • x) = b • e' x)
    (h2 : ∀ b : B, ∃ a : A, (∀ x, e (a • x) = b • e x) ∧ ∀ x, e' (a • x) = b • e' x)
    (h : SameFactors A M N) : SameFactors B M₁ N₁ := by
  obtain ⟨s, t, s0, s1, t0, t1, c, hc⟩ := h
  let o := subIso e (fun a => (h1 a).imp fun _ h => h.1) (fun a => (h2 a).imp fun _ h => h.1)
  let o' := subIso e' (fun a => (h1 a).imp fun _ h => h.2) (fun a => (h2 a).imp fun _ h => h.2)
  let s' : CompositionSeries (Submodule B M₁) :=
    { length := s.length
      toFun := fun i => o (s i)
      step := fun i => (apply_covBy_apply_iff o).mpr (s.step i) }
  let t' : CompositionSeries (Submodule B N₁) :=
    { length := t.length
      toFun := fun i => o' (t i)
      step := fun i => (apply_covBy_apply_iff o').mpr (t.step i) }
  refine ⟨s', t', ?_, ?_, ?_, ?_, c, fun i => ?_⟩
  · change o s.head = ⊥
    rw [s0, map_bot]
  · change o s.last = ⊤
    rw [s1, map_top]
  · change o' t.head = ⊥
    rw [t0, map_bot]
  · change o' t.last = ⊤
    rw [t1, map_top]
  · obtain ⟨g⟩ := hc i
    obtain ⟨f, hf⟩ := exists_subquot e (s i.succ) (s i.castSucc) (o (s i.succ)) (o (s i.castSucc))
      (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    obtain ⟨f', hf'⟩ := exists_subquot e' (t (c i).succ) (t (c i).castSucc) (o' (t (c i).succ))
      (o' (t (c i).castSucc)) (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    refine ⟨{ (f.symm.trans g.toAddEquiv).trans f' with map_smul' := fun b y => ?_ }⟩
    obtain ⟨a, ha, ha'⟩ := h2 b
    obtain ⟨z, rfl⟩ := f.surjective y
    change f' (g (f.symm (b • f z))) = b • f' (g (f.symm (f z)))
    rw [← hf a b ha, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, map_smul, hf' a b ha']

theorem sameFactors_iff (e : M ≃+ M₁) (e' : N ≃+ N₁)
    (h1 : ∀ a : A, ∃ b : B, (∀ x, e (a • x) = b • e x) ∧ ∀ x, e' (a • x) = b • e' x)
    (h2 : ∀ b : B, ∃ a : A, (∀ x, e (a • x) = b • e x) ∧ ∀ x, e' (a • x) = b • e' x) :
    SameFactors A M N ↔ SameFactors B M₁ N₁ := by
  refine ⟨sameFactors_transfer e e' h1 h2, sameFactors_transfer e.symm e'.symm (fun b => ?_) (fun a => ?_)⟩
  · obtain ⟨a, ha, ha'⟩ := h2 b
    exact ⟨a, fun x => by rw [AddEquiv.symm_apply_eq, ha, AddEquiv.apply_symm_apply],
      fun x => by rw [AddEquiv.symm_apply_eq, ha', AddEquiv.apply_symm_apply]⟩
  · obtain ⟨b, ha, ha'⟩ := h1 a
    exact ⟨b, fun x => by rw [AddEquiv.symm_apply_eq, ha, AddEquiv.apply_symm_apply],
      fun x => by rw [AddEquiv.symm_apply_eq, ha', AddEquiv.apply_symm_apply]⟩

end Transfer

section Reps
variable {O k G : Type} [CommRing O] [CommRing k] [Algebra O k] [Group G]

theorem single_smul_compat {M W : Type} [AddCommGroup M] [Module O M] [AddCommGroup W] [Module k W]
    (π : Representation O G M) (τ : Representation k G W) (e : π.asModule ≃+ τ.asModule)
    (hg : ∀ g (x : M), e (π g x) = τ g (e x))
    (hs : ∀ (a : O) (x : M), e (a • x) = (algebraMap O k a • (show W from e x) : W)) (g : G) (a : O) (x : π.asModule) :
    e ((MonoidAlgebra.single g a : MonoidAlgebra O G) • x) =
      (MonoidAlgebra.single g (algebraMap O k a) : MonoidAlgebra k G) • e x := by
  have h1 : ((MonoidAlgebra.single g a : MonoidAlgebra O G) • x : π.asModule) = (a • π g x : M) := by
    change π.asAlgebraHom (MonoidAlgebra.single g a) x = _
    simp
    rfl
  have h2 : ((MonoidAlgebra.single g (algebraMap O k a) : MonoidAlgebra k G) • e x : τ.asModule) =
      (algebraMap O k a • τ g (e x) : W) := by
    change τ.asAlgebraHom (MonoidAlgebra.single g _) (e x) = _
    simp
    rfl
  rw [h1, h2, hs]
  exact congrArg (fun y : W => algebraMap O k a • y) (hg g x)

theorem sameSS_iff_of_surjective (hk : Function.Surjective (algebraMap O k))
    {M W M' W' : Type} [AddCommGroup M] [Module O M] [AddCommGroup W] [Module k W]
    [AddCommGroup M'] [Module O M'] [AddCommGroup W'] [Module k W']
    (π : Representation O G M) (τ : Representation k G W) (e : M ≃+ W)
    (hg : ∀ g x, e (π g x) = τ g (e x)) (hs : ∀ (a : O) x, e (a • x) = algebraMap O k a • e x)
    (π' : Representation O G M') (τ' : Representation k G W') (e' : M' ≃+ W')
    (hg' : ∀ g x, e' (π' g x) = τ' g (e' x)) (hs' : ∀ (a : O) x, e' (a • x) = algebraMap O k a • e' x) :
    SameSS π π' ↔ SameSS τ τ' := by
  let E : π.asModule ≃+ τ.asModule := e
  let E' : π'.asModule ≃+ τ'.asModule := e'
  refine sameFactors_iff E E' (fun a => ?_) (fun b => ?_)
  · induction a using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, fun x => by simp, fun x => by simp⟩
    | add a a' ha ha' =>
      obtain ⟨b, h1, h2⟩ := ha
      obtain ⟨b', h3, h4⟩ := ha'
      exact ⟨b + b', fun x => by rw [add_smul, add_smul, map_add (f := _), h1, h3],
        fun x => by rw [add_smul, add_smul, map_add (f := _), h2, h4]⟩
    | single g a => exact ⟨_, single_smul_compat π τ E hg hs g a, single_smul_compat π' τ' E' hg' hs' g a⟩
  · induction b using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, fun x => by simp, fun x => by simp⟩
    | add a a' ha ha' =>
      obtain ⟨b, h1, h2⟩ := ha
      obtain ⟨b', h3, h4⟩ := ha'
      exact ⟨b + b', fun x => by rw [add_smul, add_smul, map_add (f := _), h1, h3],
        fun x => by rw [add_smul, add_smul, map_add (f := _), h2, h4]⟩
    | single g b =>
      obtain ⟨a, rfl⟩ := hk b
      exact ⟨_, single_smul_compat π τ E hg hs g a, single_smul_compat π' τ' E' hg' hs' g a⟩

end Reps

section Field
variable {k G : Type} [Field k] [Group G]

theorem brauerNesbitt : GlobalTheory.ConstituentsCompare.BrauerNesbitt := by
  intro Γ k _ _ a ρ ρ' h h' hc
  obtain ⟨P, hP⟩ := GlobalTheory.T.brauer_nesbitt_semisimple_matrix_representations a ((Units.coeHom _).comp ρ) ((Units.coeHom _).comp ρ')
    (fun W hW => (h W hW).imp fun _ h => ⟨h.2, h.1⟩) (fun W hW => (h' W hW).imp fun _ h => ⟨h.2, h.1⟩) hc
  refine ⟨P, fun g => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact Units.ext (hP g).symm

theorem charpoly_eq_cpOn {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (g : G) :
    haveI : FiniteDimensional k ρ.asModule := inferInstanceAs (FiniteDimensional k V)
    LinearMap.charpoly (ρ g) = GlobalTheory.ConsCompare.cpOn k (MonoidAlgebra.of k G g) ρ.asModule := by
  unfold GlobalTheory.ConsCompare.cpOn
  rw [← LinearEquiv.charpoly_conj ρ.asModuleEquiv]
  congr 1
  ext v
  simp [LinearEquiv.conj_apply]
  rfl

theorem sameSS_iff_charpoly {V W : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] (ρ : Representation k G V) (σ : Representation k G W) :
    SameSS ρ σ ↔ ∀ g, LinearMap.charpoly (ρ g) = LinearMap.charpoly (σ g) := by
  refine ⟨fun h g => ?_, fun h => GlobalTheory.ConsCompare.sameSS_of_charpoly_eq brauerNesbitt ρ σ h⟩
  haveI : FiniteDimensional k ρ.asModule := inferInstanceAs (FiniteDimensional k V)
  haveI : FiniteDimensional k σ.asModule := inferInstanceAs (FiniteDimensional k W)
  rw [charpoly_eq_cpOn, charpoly_eq_cpOn]
  exact GlobalTheory.ConsCompare.cpOn_eq_of_sameFactors _ h

end Field

section Lat
variable {G LL O V : Type} [Group G] [Field LL] [CommRing O] [IsDomain O] [Algebra O LL] [IsFractionRing O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [FiniteDimensional LL V]
  {ρ : Representation LL G V}

theorem charpoly_lattice (L : Lattice (O := O) ρ) [Module.Free O L.T] [Module.Finite O L.T] (g : G) :
    LinearMap.charpoly (ρ g) = (LinearMap.charpoly (latRep L g)).map (algebraMap O LL) := by
  classical
  let b := Module.Free.chooseBasis O L.T
  have hli : LinearIndependent LL (L.T.subtype ∘ b) :=
    (LinearIndependent.iff_fractionRing O LL).mp (b.linearIndependent.map' L.T.subtype L.T.ker_subtype)
  have hsum : ∀ x : L.T, (x : V) = ∑ i, algebraMap O LL (b.repr x i) • (L.T.subtype ∘ b) i := fun x => by
    conv_lhs => rw [← b.sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]
    rfl
  have hsp : ⊤ ≤ Submodule.span LL (Set.range (L.T.subtype ∘ b)) := by
    rw [← L.span, Submodule.span_le]
    intro x hx
    rw [show x = _ from hsum ⟨x, hx⟩]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let B := Module.Basis.mk hli hsp
  rw [← LinearMap.charpoly_toMatrix _ B, ← LinearMap.charpoly_toMatrix _ b, ← Matrix.charpoly_map]
  congr 1
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  have : ρ g (B j) = ∑ i, algebraMap O LL (b.repr (latRep L g (b j)) i) • B i := by
    simp only [B, Module.Basis.mk_apply]
    exact hsum (latRep L g (b j))
  rw [this, B.repr_sum_self]

end Lat

def bcRep {O G M : Type} (k : Type) [CommRing O] [CommRing k] [Algebra O k] [Group G] [AddCommGroup M] [Module O M]
    (π : Representation O G M) : Representation k G (k ⊗[O] M) :=
  (Module.End.baseChangeHom O k M).toMonoidHom.comp π

theorem sameSS_iff_map_charpoly {O k G M M' N N' : Type} [CommRing O] [Nontrivial O] [Field k] [Algebra O k]
    (hk : Function.Surjective (algebraMap O k)) [Group G] [AddCommGroup M] [Module O M]
    [Module.Free O M] [Module.Finite O M] [AddCommGroup M'] [Module O M'] [Module.Free O M'] [Module.Finite O M']
    [AddCommGroup N] [Module O N] [AddCommGroup N'] [Module O N']
    (π : Representation O G M) (π' : Representation O G M') (α : Representation O G N)
    (α' : Representation O G N') (e : N ≃ₗ[O] k ⊗[O] M) (e' : N' ≃ₗ[O] k ⊗[O] M')
    (he : ∀ g x, e (α g x) = (π g).baseChange k (e x)) (he' : ∀ g x, e' (α' g x) = (π' g).baseChange k (e' x)) :
    SameSS α α' ↔ ∀ g, (LinearMap.charpoly (π g)).map (algebraMap O k) =
      (LinearMap.charpoly (π' g)).map (algebraMap O k) := by
  refine ((sameSS_iff_of_surjective hk α (bcRep k π) e.toAddEquiv he
    (fun a x => by rw [algebraMap_smul]; exact map_smul e a x) α' (bcRep k π') e'.toAddEquiv he'
    (fun a x => by rw [algebraMap_smul]; exact map_smul e' a x)).trans (sameSS_iff_charpoly _ _)).trans ?_
  refine forall_congr' fun g => ?_
  rw [← LinearMap.charpoly_baseChange, ← LinearMap.charpoly_baseChange]
  rfl

theorem equivQuotTensor_modRep {O G N : Type} [CommRing O] [Group G] [AddCommGroup N] [Module O N]
    (α : Representation O G N) (c : O) (g : G) (x : QuotSMulTop c N) :
    QuotSMulTop.equivQuotTensor c N (modRep α c g x) =
      (α g).baseChange (O ⧸ Ideal.span {c}) (QuotSMulTop.equivQuotTensor c N x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact QuotSMulTop.equivQuotTensor_naturality_mk c (α g) x

theorem sameSS_modRep_iff {O G M M' : Type} [CommRing O] [Nontrivial O] [Group G] [AddCommGroup M] [Module O M]
    [Module.Free O M] [Module.Finite O M] [AddCommGroup M'] [Module O M'] [Module.Free O M'] [Module.Finite O M']
    (π : Representation O G M) (π' : Representation O G M') (c : O) (hc : (Ideal.span {c}).IsMaximal) :
    SameSS (modRep π c) (modRep π' c) ↔
      ∀ g j, c ∣ (LinearMap.charpoly (π g) - LinearMap.charpoly (π' g)).coeff j := by
  letI := Ideal.Quotient.field (Ideal.span {c})
  refine (sameSS_iff_map_charpoly (k := O ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective π π' _ _
    (QuotSMulTop.equivQuotTensor c M) (QuotSMulTop.equivQuotTensor c M') (equivQuotTensor_modRep π c)
    (equivQuotTensor_modRep π' c)).trans ?_
  refine forall_congr' fun g => ?_
  rw [← sub_eq_zero, ← Polynomial.map_sub, Polynomial.ext_iff]
  refine forall_congr' fun j => ?_
  rw [Polynomial.coeff_map, Polynomial.coeff_zero, ← Ideal.mem_span_singleton]
  exact Ideal.Quotient.eq_zero_iff_mem

end GlobalTheory.RedCharpoly
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleModuleIffLatticeQuotients

section

@[expose] public section

noncomputable section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open Formalism.GaloisCohomology (scalRep)
open Formalism.MainNotions.N (GRep)
open scoped Pointwise

namespace GlobalTheory.FullCharpoly

section Ref
variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (Γ : GalData G Qp LL O) (t : ℕ)

def refInt : Representation O G (↥Γ.T₀.L.T × (Fin t → O)) :=
  Γ.W₀.prod (piRep fun c : Fin t => Γ.Wchi (c.val + 1))

theorem exists_refInt_equiv :
    ∃ e : QuotSMulTop Γ.lam (↥Γ.T₀.L.T × (Fin t → O)) ≃ₗ[O]
      (QuotSMulTop Γ.lam ↥Γ.T₀.L.T × (Fin t → QuotSMulTop Γ.lam O)),
      ∀ g x, e (modRep (refInt Γ t) Γ.lam g x) = Γ.refRep t g (e x) := by
  let p : (↥Γ.T₀.L.T × (Fin t → O)) →ₗ[O] (QuotSMulTop Γ.lam ↥Γ.T₀.L.T × (Fin t → QuotSMulTop Γ.lam O)) :=
    (Submodule.mkQ _).prodMap ((Submodule.mkQ _).compLeft (Fin t))
  have hp : ∀ x, p x = (Submodule.Quotient.mk x.1, fun c => Submodule.Quotient.mk (x.2 c)) :=
    fun _ => rfl
  refine StdAdm.exists_modRep_equiv _ _ _ p ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨a, b⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    choose b' hb' using fun c => Submodule.Quotient.mk_surjective _ (b c)
    exact ⟨(a, b'), Prod.ext rfl (funext hb')⟩
  · intro x
    rw [hp, Prod.ext_iff, funext_iff]
    simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    constructor
    · rintro ⟨⟨a, ha⟩, hb⟩
      choose b hb using hb
      exact ⟨(a, b), Prod.ext ha (funext hb)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨⟨_, rfl⟩, fun c => ⟨_, rfl⟩⟩

theorem charpoly_refInt [Nontrivial O] [Module.Free O ↥Γ.T₀.L.T] [Module.Finite O ↥Γ.T₀.L.T] (g : G) :
    LinearMap.charpoly (refInt Γ t g) =
      LinearMap.charpoly (Γ.W₀ g) * ∏ c : Fin t, (X - C (Γ.chi (c.val + 1) g : O)) := by
  have h : refInt Γ t g = (Γ.W₀ g).prodMap
      (Matrix.toLin' (Matrix.diagonal fun c : Fin t => (Γ.chi (c.val + 1) g : O))) := by
    refine LinearMap.ext fun x => Prod.ext rfl (funext fun c => ?_)
    change (Γ.chi (c.val + 1) g : O) • x.2 c = Matrix.mulVec _ x.2 c
    rw [Matrix.mulVec_diagonal, smul_eq_mul]
  rw [h, LinearMap.charpoly_prodMap, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]

theorem sameSS_refRep_iff [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]
    (hlam : Irreducible Γ.lam) {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    [FiniteDimensional LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ) :
    SameSS (modRep (latRep L) Γ.lam) (Γ.refRep t) ↔ ∀ g j, ∃ y : O,
      (LinearMap.charpoly (ρ g) - LinearMap.charpoly (Γ.T₀.ρ g) *
        ∏ c : Fin t, (X - C (algebraMap O LL (Γ.chi (c.val + 1) g)))).coeff j = algebraMap O LL (Γ.lam * y) := by
  have := L.free
  have := Γ.T₀.L.free
  have : Module.Finite O L.T := Module.Finite.iff_fg.2 L.fg
  have : Module.Finite O Γ.T₀.L.T := Module.Finite.iff_fg.2 Γ.T₀.L.fg
  obtain ⟨e, he⟩ := exists_refInt_equiv Γ t
  have h1 : SameSS (modRep (latRep L) Γ.lam) (Γ.refRep t) ↔
      SameSS (modRep (latRep L) Γ.lam) (modRep (refInt Γ t) Γ.lam) :=
    ⟨fun h => StdAdm.sameSS_of_equiv h e.symm fun g x => by
      rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply],
     fun h => StdAdm.sameSS_of_equiv h e he⟩
  rw [h1, GlobalTheory.RedCharpoly.sameSS_modRep_iff _ _ _ (PrincipalIdealRing.isMaximal_of_irreducible hlam)]
  refine forall_congr' fun g => forall_congr' fun j => exists_congr fun y => ?_
  have h2 : ∏ c : Fin t, (X - C (algebraMap O LL (Γ.chi (c.val + 1) g))) =
      (∏ c : Fin t, (X - C (Γ.chi (c.val + 1) g : O))).map (algebraMap O LL) := by
    simp [Polynomial.map_prod]
  rw [GlobalTheory.RedCharpoly.charpoly_lattice L, GlobalTheory.RedCharpoly.charpoly_lattice Γ.T₀.L, h2, ← Polynomial.map_mul,
    ← Polynomial.map_sub, Polynomial.coeff_map, charpoly_refInt]
  exact (IsFractionRing.injective O LL).eq_iff.symm

end Ref

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

theorem full_iff (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) :
    Full (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut T ↔ CrysWith (P.PD S.K) S.emb T.ρ S.D.Ut ∧ ∀ g j, ∃ y : S.O,
      (LinearMap.charpoly (T.ρ g) - LinearMap.charpoly (S.Γ.T₀.ρ g) *
        ∏ c : Fin S.D.t, (X - C (algebraMap S.O ↥S.LL.1 (S.Γ.chi (c.val + 1) g)))).coeff j =
          algebraMap S.O ↥S.LL.1 (S.Γ.lam * y) := by
  obtain ⟨⟨_, h1, h2⟩, -, -, h3, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  have hlam : Irreducible S.Γ.lam := S.hyp.1.2.2.2.2.2
  exact and_congr_right fun _ => ⟨fun h => (sameSS_refRep_iff S.Γ S.D.t hlam T.L).1 (h T.L),
    fun h L => (sameSS_refRep_iff S.Γ S.D.t hlam L).2 h⟩

theorem hasFiniteQuotients_padicInt : Ring.HasFiniteQuotients ℤ_[l] where
  finiteQuotient {I} hI := by
    obtain ⟨n, rfl⟩ := PadicInt.ideal_eq_span_pow_p hI
    rw [← PadicInt.ker_toZModPow]
    exact Finite.of_injective _ (RingHom.kerLift_injective (PadicInt.toZModPow n))

theorem hasFiniteQuotients_OL (LL : FinExt l) : Ring.HasFiniteQuotients ↥(OL LL) := by
  have := hasFiniteQuotients_padicInt (l := l)
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : Module.Finite ℤ_[l] ↥(OL LL) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 (integralClosure ℤ_[l] ↥LL.1)
  exact Ring.HasFiniteQuotients.of_module_finite ℤ_[l] _

theorem finite_of_lattices {G LL O V M : Type} [Group G] [Field LL] [CommRing O] [IsDomain O] [Algebra O LL]
    [IsFractionRing O LL] [Ring.HasFiniteQuotients O] [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] [AddCommGroup M] [Module O M] {ρ : Representation LL G V}
    (L₁ L₂ : Lattice (O := O) ρ) (p : ↥L₁.T →ₗ[O] M) (hp : Function.Surjective p)
    (hk : ∀ x : ↥L₁.T, (x : V) ∈ L₂.T → p x = 0) : Finite M := by
  have : Module.Finite O L₁.T := Module.Finite.iff_fg.2 L₁.fg
  have : Module.Finite O M := Module.Finite.of_surjective p hp
  have h1 : ∀ x : V, ∃ a : nonZeroDivisors O, (a : O) • x ∈ L₂.T := by
    intro x
    have hx : x ∈ Submodule.span LL (L₂.T : Set V) := by rw [L₂.span]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, by simpa using hx⟩
    | zero => exact ⟨1, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a * b, ?_⟩
      rw [smul_add, Submonoid.coe_mul]
      refine L₂.T.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact L₂.T.smul_mem _ ha
      · rw [mul_smul]; exact L₂.T.smul_mem _ hb
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨⟨y, b⟩, hb⟩ := IsLocalization.surj (nonZeroDivisors O) c
      refine ⟨a * b, ?_⟩
      have : ((a * b : nonZeroDivisors O) : O) • c • x = y • ((a : O) • x) := by
        rw [Submonoid.coe_mul, mul_smul, smul_comm y, ← algebraMap_smul LL (b : O), smul_smul, mul_comm, hb,
          algebraMap_smul]
      rw [this]
      exact L₂.T.smul_mem _ ha
  have ht : Module.IsTorsion O M := by
    intro m
    obtain ⟨x, rfl⟩ := hp m
    obtain ⟨a, ha⟩ := h1 x
    exact ⟨a, by rw [Submonoid.smul_def, ← map_smul]; exact hk _ ha⟩
  obtain ⟨r, hr, hr0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors ht
  have : Finite (O ⧸ Ideal.span {r}) := Ring.HasFiniteQuotients.finiteQuotient
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact nonZeroDivisors.ne_zero hr0)
  have hb : Ideal.span {r} • (⊤ : Submodule O M) = ⊥ :=
    Submodule.le_annihilator_iff.1 ((Ideal.span_singleton_le_iff_mem _).2 hr)
  have : Finite (M ⧸ Ideal.span {r} • (⊤ : Submodule O M)) :=
    Submodule.finite_quotient_smul _ Module.Finite.fg_top
  exact Finite.of_equiv _ (Submodule.quotEquivOfEqBot _ hb).toEquiv

attribute [local instance 10000] GRep.modO LocLat.modO GRep.towO LocLat.towO Submodule.module

theorem nonempty_lattice (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O) : Nonempty (Lattice (O := S.O) A.ρ) := by
  obtain ⟨⟨_, h1, h2⟩, -, -, h3, h4⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  have := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK S.K
  exact GlobalTheory.CrysExt.exists_lattice h4 A.ρ A.cont

def PolyFull (jT : ZMod S.n → ℤ → ℤ) (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O) : Prop :=
  IsCrys (P.PD S.K) A.ρ ∧
    (∀ i (τ : ↥S.K.1 →ₐ[ℚ_[l]] ↥S.LL.1), (∀ x : ↥(K0 S.K), τ (algebraMap _ _ x) = S.emb i x) →
      ∀ a : ℤ, multV (P.PD S.K) A.ρ τ a = jT i a) ∧
    ∀ g j, ∃ y : S.O, (LinearMap.charpoly (A.ρ g) - LinearMap.charpoly (S.Γ.T₀.ρ g) *
      ∏ c : Fin S.D.t, (X - C (algebraMap S.O ↥S.LL.1 (S.Γ.chi (c.val + 1) g)))).coeff j =
        algebraMap S.O ↥S.LL.1 (S.Γ.lam * y)

def toLoc (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O) (L : Lattice (O := S.O) A.ρ) : LocLat S.G ℚ_[l] ↥S.LL.1 S.O where
  V := A.V
  ρ := A.ρ
  cont := A.cont
  L := L

def ofLoc (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) : GRep S.G ℚ_[l] ↥S.LL.1 S.O where
  V := T.V
  ρ := T.ρ
  cont := T.cont

theorem full_iff_polyFull {jT : ZMod S.n → ℤ → ℤ} (hj : ∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a)
    (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) :
    Full (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut T ↔ PolyFull S jT (ofLoc S T) := by
  rw [full_iff, CrysWith, and_assoc]
  simp only [HasJumps, hj]
  rfl



theorem admissibleModule_iff_lattice_quotients {jT : ZMod S.n → ℤ → ℤ} (hj : ∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a)
    {M : Type} [AddCommGroup M] [Module S.O M] (π : Representation S.O S.G M) :
    S.admitted π ↔ ∃ (μ : ℕ) (F : Fin μ → GRep S.G ℚ_[l] ↥S.LL.1 S.O) (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O)
      (e : A.V ≃ₗ[↥S.LL.1] (∀ j, (F j).V)) (L₁ L₂ : Lattice (O := S.O) A.ρ) (p : ↥L₁.T →ₗ[S.O] M),
      (∀ j, PolyFull S jT (F j)) ∧ (∀ g x j, e (A.ρ g x) j = (F j).ρ g (e x j)) ∧ L₂.T ≤ L₁.T ∧
      Function.Surjective p ∧ (∀ g x, p (latRep L₁ g x) = π g (p x)) ∧ ∀ x, p x = 0 ↔ (x : A.V) ∈ L₂.T := by
  constructor
  · rintro ⟨-, μ, T, ⟨F, hF, e, he⟩, L₂, p, h1, h2, h3, h4⟩
    exact ⟨μ, fun j => ofLoc S (F j), ofLoc S T, e, T.L, L₂, p,
      fun j => (full_iff_polyFull S hj _).1 (hF j), he, h1, h2, h3, h4⟩
  · rintro ⟨μ, F, A, e, L₁, L₂, p, hF, he, h1, h2, h3, h4⟩
    obtain ⟨⟨_, -, h6⟩, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
    have := hasFiniteQuotients_OL S.LL
    exact ⟨finite_of_lattices L₁ L₂ p h2 fun x => (h4 x).2, μ, toLoc S A L₁,
      ⟨fun j => toLoc S (F j) (nonempty_lattice S (F j)).some,
        fun j => (full_iff_polyFull S hj _).2 (hF j), e, he⟩, L₂, p, h1, h2, h3, h4⟩

end GlobalTheory.FullCharpoly
end
end
end
