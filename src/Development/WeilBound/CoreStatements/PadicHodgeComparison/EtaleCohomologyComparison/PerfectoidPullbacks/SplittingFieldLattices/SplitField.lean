module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasisBOfBcOn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapOAffine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingOverLatticeBaseStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarMultiplicationShiftsFiltrationStatement
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingOverField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftPOfBounds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PdPBotPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarMultiplicationShiftsFiltration
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijectiveStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Mathlib.RingTheory.Coalgebra.CoassocSimps

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFgPullSqC

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatticeFinite

universe u v u' v'

section General

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {R' : Type} [CommRing R'] {C' : Type u'} [Category.{v'} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'}

theorem pull_sqC_comb (m : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} {c c₁ c₂ e e' : R'}
    (hc : c = e * c₁ + e' * c₂) (ha : m.LeC c a a') (hb : m.LeC c b b') (ha₁ : m.LeC c₁ a a') (hb₁ : m.LeC c₁ b b')
    (ha₂ : m.LeC c₂ a a') (hb₂ : m.LeC c₂ b b') (j : ℕ) (x : CH.H (sq a b) j) :
    (m.sqC c ha hb).pull j x =
      e • (m.sqC c₁ ha₁ hb₁).pull j x + e' • (m.sqC c₂ ha₂ hb₂).pull j x := by
  obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk _ = e • Submodule.Quotient.mk _ + e' • Submodule.Quotient.mk _
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  refine congrArg _ (Subtype.ext (funext fun s => ?_))
  change (m.sqC c ha hb).τ _ (f (s ⋙ m.G)) =
    e • (m.sqC c₁ ha₁ hb₁).τ _ (f (s ⋙ m.G)) + e' • (m.sqC c₂ ha₂ hb₂).τ _ (f (s ⋙ m.G))
  generalize f (s ⋙ m.G) = w
  obtain ⟨z, hz⟩ := w
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine Subtype.ext ?_
  have key : algebraMap R' (Φ'.A.obj (s.obj (Fin.last j))) c * m.ρ (s.obj (Fin.last j)) y =
      e • (algebraMap R' (Φ'.A.obj (s.obj (Fin.last j))) c₁ * m.ρ (s.obj (Fin.last j)) y) +
      e' • (algebraMap R' (Φ'.A.obj (s.obj (Fin.last j))) c₂ * m.ρ (s.obj (Fin.last j)) y) := by
    rw [hc, map_add (f := _), map_mul, map_mul, Algebra.smul_def, Algebra.smul_def]
    ring
  exact congrArg (Ideal.Quotient.mk (b'.S (s.obj (Fin.last j)))) key

theorem exists_fg_pull_sqC (m : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (P : Ideal R') (hP : P.FG)
    (h₁ : ∀ c ∈ P, m.LeC c a a') (h₂ : ∀ c ∈ P, m.LeC c b b') (j : ℕ) (hfin : Module.Finite R (CH.H (sq a b) j)) :
    ∃ N : Submodule R' (CH.H (sq a' b') j), N.FG ∧ ∀ (c : R') (ha : m.LeC c a a') (hb : m.LeC c b b'), c ∈ P →
      ∀ x, (m.sqC c ha hb).pull j x ∈ N := by
  classical
  obtain ⟨G, rfl⟩ := hP
  obtain ⟨X, hX⟩ := (Module.Finite.fg_top : (⊤ : Submodule R (CH.H (sq a b) j)).FG)
  let φ : G × X → CH.H (sq a' b') j := fun p =>
    (m.sqC p.1.1 (h₁ _ (Ideal.subset_span p.1.2)) (h₂ _ (Ideal.subset_span p.1.2))).pull j p.2.1
  refine ⟨Submodule.span R' (Set.range φ), Submodule.fg_span (Set.finite_range φ), ?_⟩
  have hgen : ∀ (g : R') (hg : g ∈ G) (ha : m.LeC g a a') (hb : m.LeC g b b') (x : CH.H (sq a b) j),
      (m.sqC g ha hb).pull j x ∈ Submodule.span R' (Set.range φ) := by
    intro g hg ha hb x
    have hx : x ∈ Submodule.span R (X : Set (CH.H (sq a b) j)) := hX ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨(⟨g, hg⟩, ⟨x, hx⟩), rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  intro c ha hb hc x
  refine Submodule.span_induction
    (p := fun c _ => ∀ (ha : m.LeC c a a') (hb : m.LeC c b b'), (m.sqC c ha hb).pull j x ∈ Submodule.span R' (Set.range φ))
    ?_ ?_ ?_ ?_ hc ha hb
  · intro g hg ha hb
    exact hgen g hg ha hb x
  · intro ha hb
    rw [pull_sqC_comb m (c₁ := 0) (c₂ := 0) (e := 0) (e' := 0) (by simp) ha hb ha hb ha hb j x]
    simp
  · intro c₁ c₂ m₁ m₂ i₁ i₂ ha hb
    rw [pull_sqC_comb m (c₁ := c₁) (c₂ := c₂) (e := 1) (e' := 1) (by simp) ha hb (h₁ _ m₁) (h₂ _ m₁) (h₁ _ m₂) (h₂ _ m₂) j x]
    simpa using add_mem (i₁ (h₁ _ m₁) (h₂ _ m₁)) (i₂ (h₁ _ m₂) (h₂ _ m₂))
  · intro e c₁ m₁ i₁ ha hb
    rw [pull_sqC_comb m (c₁ := c₁) (c₂ := c₁) (e := e) (e' := 0) (by simp) ha hb (h₁ _ m₁) (h₂ _ m₁) (h₁ _ m₁) (h₂ _ m₁) j x]
    simpa using Submodule.smul_mem _ e (i₁ (h₁ _ m₁) (h₂ _ m₁))

end General

theorem dividedPowerFiltration_anti {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {r r' : ℕ} (h : r ≤ r') :
    pdP δ r' ≤ pdP δ r :=
  Ideal.span_mono fun _ ⟨l, h₁, h₂, h₃⟩ => ⟨l, h₁, h.trans h₂, h₃⟩

theorem tfBase_mono {B : Type} [CommRing B] {J : Ideal B} {δ : DividedPowers J} {l m s : ℕ} (h : TFBase δ l m)
    (hms : m ≤ s) : TFBase δ l s :=
  ⟨le_bot_iff.1 (h.nil ▸ dividedPowerFiltration_anti δ hms), h.tf, h.dv⟩

theorem afgA_of_bcOn_finO : BcOn False → FinO → AfgA := by
  intro hB hF O A _ _ _ _ _ I γ l s m hl hO hL hms X q _ U 𝒱 h𝒱 r r' hr hr' j
  obtain ⟨S⟩ := GlobalTheory.T.graded_splitting_over_lattice_base γ l m hl hL
  have hA : TFBase γ l s := tfBase_mono hL.tf hms
  have hC : ∀ (i : Fin m) (t : ℤ) (c : A), c ∈ pdP γ i →
      (smO γ q l s 𝒱).LeC c (sFil _ (t - i)) (sFil _ t) :=
    fun i t c hc => GlobalTheory.T.scalar_multiplication_shifts_filtration γ q l s 𝒱 i c hc t
  have ha : ∀ (i : Fin m) n, (smO γ q l s 𝒱).LeC (S.ν i n) (sFil _ (r - i)) (sFil _ r) :=
    fun i n => hC i r _ (S.mem i n)
  have hb : ∀ (i : Fin m) n, (smO γ q l s 𝒱).LeC (S.ν i n) (sFil _ (r' - i)) (sFil _ r') :=
    fun i n => hC i r' _ (S.mem i n)
  obtain ⟨g, hg⟩ := hB γ l s m hO hA S q 𝒱 (Or.inr ⟨not_false, ⟨U⟩, h𝒱⟩) r r' hr hr' ha hb j
  have hN : ∀ i : Fin m, ∃ N : Submodule A (HQ (TS γ q l s 𝒱) r r' j), N.FG ∧
      ∀ n x, ((smO γ q l s 𝒱).sqC (S.ν i n) (ha i n) (hb i n)).pull j x ∈ N := by
    intro i
    have hi : (0 : ℤ) ≤ (i : ℕ) := Int.natCast_nonneg _
    obtain ⟨N, h₁, h₂⟩ := exists_fg_pull_sqC (smO γ q l s 𝒱) (pdP γ i) (hL.fg i) (fun c hc => hC i r c hc)
      (fun c hc => hC i r' c hc) j (hF l s hO q U 𝒱 h𝒱 (r - i) (r' - i) (by omega) (by omega) j)
    exact ⟨N, h₁, fun n x => h₂ _ _ _ (S.mem i n) x⟩
  choose N hNfg hNmem using hN
  refine ⟨0, ⨆ i, N i, Submodule.fg_iSup _ hNfg, fun y => ?_⟩
  rw [pow_zero, one_smul]
  have hsingle : ∀ (i : Fin m) (t : S.N i ⊗[O] HQ (TO q l s 𝒱) (r - i) (r' - i) j),
      g (Pi.single i t) ∈ ⨆ i, N i := by
    intro i t
    induction t using TensorProduct.inductionOn with
    | tmul n x => rw [hg]; exact Submodule.mem_iSup_of_mem i (hNmem i n x)
    | add t t' ht ht' => rw [Pi.single_add, map_add (f := _)]; exact add_mem ht ht'
  have hy : y = ∑ i, g (Pi.single i (g.symm y i)) := by

    rw [← map_sum, Finset.univ_sum_single, g.apply_symm_apply]
  rw [hy]
  exact sum_mem fun i _ => hsingle i _

end GlobalTheory.CompanionTheory.LatticeFinite
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensTransportSymm

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.GlobBc

universe w w'

theorem tens_transport {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] {M M₁ : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] {M' M₁' : Type w'} [AddCommGroup M'] [AddCommGroup M₁']
    {f : ∀ i, N i → M i → M'} {f₁ : ∀ i, N i → M₁ i → M₁'}
    (e : ∀ i, M i ≃ₗ[R] M₁ i) (e' : M' ≃+ M₁') (h : ∀ i n x, e' (f i n x) = f₁ i n (e i x))
    (hT : Tens R f) : Tens R f₁ := by
  obtain ⟨g, hg⟩ := hT
  let c : (∀ i, N i ⊗[R] M₁ i) ≃+ (∀ i, N i ⊗[R] M i) :=
    AddEquiv.piCongrRight fun i => (TensorProduct.congr (LinearEquiv.refl R (N i)) (e i).symm).toAddEquiv
  refine ⟨c.trans (g.trans e'), fun i n x => ?_⟩
  have hc : c (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ (e i).symm x) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [c]
    · simp [c, Pi.single_eq_of_ne hk]
  simp only [AddEquiv.trans_apply]
  rw [hc, hg, h, LinearEquiv.apply_symm_apply]

theorem tens_transport_symm {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] {M M₁ : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] {M' M₁' : Type w'} [AddCommGroup M'] [AddCommGroup M₁']
    {f : ∀ i, N i → M i → M'} {f₁ : ∀ i, N i → M₁ i → M₁'}
    (e : ∀ i, M i ≃ₗ[R] M₁ i) (e' : M' ≃+ M₁') (h : ∀ i n x, e' (f i n x) = f₁ i n (e i x))
    (hT : Tens R f₁) : Tens R f :=
  tens_transport (fun i => (e i).symm) e'.symm
    (fun i n x => by rw [AddEquiv.symm_apply_eq, h, LinearEquiv.apply_symm_apply]) hT

section
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O))

def thM : SMor (thP (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))) (thP (nlFun γ 0 X q (κA O I)))
    (algebraMap O A) where
  G := ((nmO γ q).mor 0).functor
  ρ T := RingHom.id _
  comm _ _ := rfl
  nat _ _ := rfl
  mem _ _ hx := hx
  dp _ _ _ _ := rfl

theorem leC {c : A} {i : ℕ} (hc : c ∈ pdP γ i) (r : ℤ) :
    (thM γ q).LeC c (thFil _ (r - i)) (thFil _ r) := by
  intro T x hx
  have h1 : T.i c ∈ pdP T.δ i := dividedPowerFiltration_map T.compat i hc
  have h2 : x ∈ pdP T.δ (r - i).toNat := hx
  have h3 := GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.δ _ _ (Ideal.mul_mem_mul h1 h2)
  exact T.pdPow_anti (by omega) h3

end

abbrev rq {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) :
    CH.Mor (sq (sFil Q r) (sFil Q r')) (sq (sFil Q' r) (sFil Q' r')) (RingHom.id _) :=
  (incl h).sq (incl_fil h r) (incl_fil h r')

section
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) {m : ℕ} (S : GrSplit O γ m)

theorem leS (𝒱 : Set X.Opens) (i : Fin m) (n : S.N i) (r : ℤ) :
    (smO γ q l s 𝒱).LeC (S.ν i n) (sFil _ (r - i)) (sFil _ r) :=
  fun T x hx => leC γ q (S.mem i n) r T.obj x hx

abbrev mC (𝒱 : Set X.Opens) (r r' : ℤ) (i : Fin m) (n : S.N i) :=
  (smO γ q l s 𝒱).sqC (S.ν i n) (leS γ q l s S 𝒱 i n r) (leS γ q l s S 𝒱 i n r')

def BcAt (𝒱 : Set X.Opens) (r r' : ℤ) (j : ℕ) : Prop :=
  Tens O (N := S.N) (M := fun i => HQ (TO q l s 𝒱) (r - i) (r' - i) j) (M' := HQ (TS γ q l s 𝒱) r r' j)
    fun i n x => (mC γ q l s S 𝒱 r r' i n).pull j x

variable {γ q l s}

theorem st_top {R : Type} [CommRing R] {J : Ideal R} {δ : DividedPowers J} {p : ℕ} {κ : O →+* R ⧸ J}
    (Q : ObjectProperty (Thick (nlFun δ p X q κ))) (𝒱 : Set X.Opens) : St Q 𝒱 ≤ St Q {⊤} := by
  rintro T ⟨h, V, -, -⟩
  exact ⟨h, ⊤, rfl, fun _ _ => trivial⟩

theorem comm_top (𝒱 : Set X.Opens) (r r' : ℤ) (j : ℕ) (i : Fin m) (n : S.N i) (x) :
    (rq (st_top (TF l s) 𝒱) r r').pull j ((mC γ q l s S {⊤} r r' i n).pull j x) =
    (mC γ q l s S 𝒱 r r' i n).pull j ((rq (st_top (TF l s) 𝒱) (r - i) (r' - i)).pull j x) := by
  refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap O A) (mC γ q l s S {⊤} r r' i n) (rq (st_top (TF l s) 𝒱) r r') j x).1).symm.trans
    (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap O A) (rq (st_top (TF l s) 𝒱) (r - i) (r' - i)) (mC γ q l s S 𝒱 r r' i n) j x).1))
  refine CrystallineSemistableComparison.P.prism (σ := algebraMap O A) ((mC γ q l s S {⊤} r r' i n).comp (rq (st_top (TF l s) 𝒱) r r'))
    ((rq (st_top (TF l s) 𝒱) (r - i) (r' - i)).comp (mC γ q l s S 𝒱 r r' i n)) (𝟙 _) (fun T y => ?_) j x
  obtain ⟨y, hy⟩ := y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  first
    | rfl
    | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)

theorem used_TF {R : Type} [CommRing R] {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} (l s : ℕ) :
    Used (TF l s : ObjectProperty (Thick (nlFun δ 0 X q κ))) :=
  Or.inl ⟨rfl, l, s, rfl⟩

theorem bcAt_iff (𝒱 : Set X.Opens) (h𝒱 : sSup 𝒱 = ⊤) (r r' : ℤ) (j : ℕ) :
    BcAt γ q l s S {⊤} r r' j ↔ BcAt γ q l s S 𝒱 r r' j := by
  have hc : ∀ W ∈ ({⊤} : Set X.Opens), W ≤ sSup 𝒱 := fun W hW => by rw [h𝒱]; exact le_top
  have bO := (GlobalTheory.T.cech_refinement_cohomology_bijective (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk (⊥ : Ideal O)) (TF l s) (used_TF l s) 𝒱 {⊤} (st_top _ _) hc j).1
  have bA := (GlobalTheory.T.cech_refinement_cohomology_bijective (γ := γ) (p := 0) (q := q) (κ := κA O I) (TF l s) (used_TF l s) 𝒱 {⊤} (st_top _ _) hc j).1
  let eO : ∀ i : Fin m, HQ (TO q l s {⊤}) (r - i) (r' - i) j ≃ₗ[O] HQ (TO q l s 𝒱) (r - i) (r' - i) j := fun i =>
    LinearEquiv.ofBijective ((rq (st_top (TF l s) 𝒱) (r - i) (r' - i)).pull j) (bO _ _)
  let eA : HQ (TS γ q l s {⊤}) r r' j ≃+ HQ (TS γ q l s 𝒱) r r' j :=
    (LinearEquiv.ofBijective ((rq (st_top (TF l s) 𝒱) r r').pull j) (bA _ _)).toAddEquiv
  have hcomm : ∀ i n x, eA ((mC γ q l s S {⊤} r r' i n).pull j x) = (mC γ q l s S 𝒱 r r' i n).pull j (eO i x) :=
    fun i n x => comm_top S 𝒱 r r' j i n x
  exact ⟨tens_transport eO eA hcomm, tens_transport_symm eO eA hcomm⟩

end

section
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {m : ℕ} (S : GrSplit O γ m)

abbrev thO (q : X ⟶ Spec (CommRingCat.of O)) (r r' : ℤ) :
    Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) ⥤ ModuleCat.{0} O :=
  sq (thFil _ r) (thFil _ r')

abbrev thS (r r' : ℤ) : Thick (nlFun γ 0 X q (κA O I)) ⥤ ModuleCat.{0} A :=
  sq (thFil _ r) (thFil _ r')

abbrev tM (r r' : ℤ) (i : Fin m) (n : S.N i) : CH.Mor (thO q (r - i) (r' - i)) (thS γ q r r') (algebraMap O A) :=
  (thM γ q).sqC (S.ν i n) (leC γ q (S.mem i n) r) (leC γ q (S.mem i n) r')

theorem tM_add (r r' : ℤ) (i : Fin m) (n n' : S.N i) (T) (x) :
    (tM γ q S r r' i (n + n')).τ T x = (tM γ q S r r' i n).τ T x + (tM γ q S r r' i n').τ T x := by
  obtain ⟨y, hy⟩ := x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine Subtype.ext ?_
  let B := (thA (nlFun γ 0 X q (κA O I))).obj T
  let z' : B := z
  have e : algebraMap A B (S.ν i (n + n')) * z' = algebraMap A B (S.ν i n) * z' + algebraMap A B (S.ν i n') * z' := by
    rw [map_add (f := _), map_add (f := _), add_mul]
  exact congrArg (Ideal.Quotient.mk ((thFil (nlFun γ 0 X q (κA O I)) r').S T)) e

theorem tM_smul (r r' : ℤ) (i : Fin m) (c : O) (n : S.N i) (T) (x) :
    (tM γ q S r r' i (c • n)).τ T x = algebraMap O A c • (tM γ q S r r' i n).τ T x := by
  obtain ⟨y, hy⟩ := x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine Subtype.ext ?_
  let B := (thA (nlFun γ 0 X q (κA O I))).obj T
  let z' : B := z
  have e : algebraMap A B (S.ν i (c • n)) * z' = algebraMap O A c • (algebraMap A B (S.ν i n) * z') := by
    rw [map_smul, Algebra.smul_def c, map_mul, mul_assoc, Algebra.smul_def (algebraMap O A c)]
  exact congrArg (Ideal.Quotient.mk ((thFil (nlFun γ 0 X q (κA O I)) r').S T)) e

end

theorem main : KH.GlobBcSt → BcOn True → BcOn False := by
  intro hG hT O A _ _ _ I γ l s m hO hA S X q 𝒱 hc r r' hrr hr's ha hb j
  obtain ⟨U, h𝒱⟩ : Nonempty (Cov q) ∧ sSup 𝒱 = ⊤ := by
    rcases hc with ⟨h, -⟩ | ⟨-, h⟩
    · exact h.elim
    · exact h
  obtain ⟨U⟩ := U
  have hU : sSup (Set.range U.U) = ⊤ := by rw [sSup_range]; exact U.cover
  have hmem : ∀ (𝒲 : Set X.Opens) (T), St (TF l s) 𝒲 T → St (TF l s) 𝒲 ((((nmO γ q).mor 0).functor).obj T) :=
    fun 𝒲 T h => nmO_mem γ q l s 𝒲 T h
  have key : ∀ j, BcAt γ q l s S (Set.range U.U) r r' j := fun j =>
    hG (O := O) (R := O) (I := ⊥) (γ := dividedPowersBot O) (p := 0) (X := X) (q := q) (κ := Ideal.Quotient.mk ⊥)
      (O' := O) (R' := A) (I' := I) (γ' := γ) (p' := 0) (X' := X) (q' := q) (κ' := κA O I)
      (Λ := O) (Λ' := A) (σ := algebraMap O A) ((nmO γ q).mor 0).functor S.N
      (fun i => thO q (r - i) (r' - i)) (thS γ q r r')
      (fun i n T => (tM γ q S r r' i n).τ T) (fun i n {T T'} φ x => (tM γ q S r r' i n).nat φ x)
      (fun i n n' T x => tM_add γ q S r r' i n n' T x) (fun i c n T x => tM_smul γ q S r r' i c n T x)
      (TF l s) (TF l s) U.U U.U (fun α T h => hmem _ T h) (fun S' T h => hmem _ T h) (fun T h => hmem _ T h)
      (fun S' hS' j => by
        obtain ⟨α, hα⟩ := hS'
        obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (U.c α) (iInf₂_le α hα : (⨅ α ∈ S', U.U α) ≤ U.U α) (U.inter S' ⟨α, hα⟩)
        exact hT γ l s m hO hA S q {⨅ α ∈ S', U.U α} (Or.inl ⟨trivial, _, _, rfl, ⟨c'⟩⟩) r r' hrr hr's
          (fun i n => leS γ q l s S _ i n r) (fun i n => leS γ q l s S _ i n r') j) j
  exact (bcAt_iff S 𝒱 h𝒱 r r' j).1 ((bcAt_iff S (Set.range U.U) hU r r' j).2 (key j))

end GlobalTheory.CompanionTheory.GlobBc
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.SplitField

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

theorem split_field : ∀ {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) (m : ℕ),
    pdP γ m = ⊥ → Nonempty (GrSplit K γ m) := @GlobalTheory.CompanionTheory.GrSplitField.nonempty_grSplit

theorem leC_shift : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens) (i : ℕ) (a : A), a ∈ pdP γ i → ∀ r : ℤ,
    (smO γ q l s 𝒱).LeC a (sFil _ (r - i)) (sFil _ r) := @GlobalTheory.CompanionTheory.LecShift.leC_shift

theorem bc_loc : KH.LocBc → KH.PolyTf → BcOn True := @GlobalTheory.CompanionTheory.BcLoc.bc_single

theorem bc_glob : KH.GlobBcSt → BcOn True → BcOn False := @GlobalTheory.CompanionTheory.GlobBc.main

theorem fin_o : KH.LocGr → KH.PolyTf → KH.GlobSerreSt → KH.GrCechFin → FinO := @GlobalTheory.CompanionTheory.FinOverO.finO

theorem afg_a : BcOn False → FinO → AfgA := @GlobalTheory.CompanionTheory.LatticeFinite.afgA_of_bcOn_finO

theorem lift_a : AfgA → LiftA := @GlobalTheory.CompanionTheory.LiftLat.liftA_of_afgA

theorem basis_b : BcOn False → KH.KIso → BasisB := @GlobalTheory.CompanionTheory.BasisBase.basisB_of_bcOn

end CrystallineSemistableComparison.Pb
end
end
end
