module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
public import Mathlib.Algebra.DualNumber
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.SimpleRing.Principal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPowSt

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotLeSqSup

section

@[expose] public section

namespace GlobalTheory.NotLeSqSup

theorem not_le_sq_sup {A : Type} [CommRing A] {m I : Ideal A} {n : ℕ}
    (hn : m ^ (n + 1) = ⊥) (hI : ¬ m ≤ I) : ¬ m ≤ m ^ 2 ⊔ I := by
  intro h
  have key : ∀ j : ℕ, m ≤ m ^ (j + 1) ⊔ I := by
    intro j
    induction j with
    | zero => simpa using (le_sup_left : m ≤ m ⊔ I)
    | succ j ih =>
      calc m ≤ m ^ 2 ⊔ I := h
        _ ≤ m ^ (j + 1 + 1) ⊔ I := by
          refine sup_le ?_ le_sup_right
          calc m ^ 2 = m * m := pow_two m
            _ ≤ m * (m ^ (j + 1) ⊔ I) := Ideal.mul_mono_right ih
            _ = m * m ^ (j + 1) ⊔ m * I := Ideal.mul_sup _ _ _
            _ ≤ m ^ (j + 1 + 1) ⊔ I :=
              sup_le_sup (le_of_eq (pow_succ' m (j + 1)).symm)
                (Ideal.mul_le.mpr fun r _ s hs => I.mul_mem_left r hs)
  apply hI
  simpa [hn] using key n

theorem main : ∀ {k A : Type} [inst : Field k] [inst_1 : CommRing A] [inst_2 : Algebra k A] (aug : A →ₐ[k] k) {I : Ideal A} {n : ℕ}, RingHom.ker aug ^ (n + (1 : ℕ)) = ⊥ → I ≤ RingHom.ker aug → ¬RingHom.ker aug ≤ I → ∃ (φ : A →ₐ[k] DualNumber k), AlgHom.comp (TrivSqZeroExt.fstHom k k k) φ = aug ∧ (∀ a ∈ I, (φ : A → DualNumber k) a = (0 : DualNumber k)) ∧ ∃ a ∈ RingHom.ker aug, (φ : A → DualNumber k) a ≠ (0 : DualNumber k) := by
  intro k A _ _ _ aug I n hn hIm hmI
  have hx : ¬ RingHom.ker aug ≤ RingHom.ker aug ^ 2 ⊔ I := not_le_sq_sup hn hmI
  obtain ⟨x, hxm, hxN⟩ := Set.not_subset.mp hx
  let N : Submodule k A := (RingHom.ker aug ^ 2 ⊔ I).restrictScalars k
  have hq : N.mkQ x ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hxN
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual k (A ⧸ N), f (N.mkQ x) ≠ 0 := by
    by_contra h; push_neg at h
    exact hq ((Module.forall_dual_apply_eq_zero_iff k _).mp h)
  let g : A →ₗ[k] k := f.comp N.mkQ
  have hgN : ∀ a ∈ RingHom.ker aug ^ 2 ⊔ I, g a = 0 := by
    intro a ha
    have : N.mkQ a = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact ha
    simp only [g, LinearMap.comp_apply, this, map_zero]
  let D : A →ₗ[k] k := g.comp (LinearMap.id - (Algebra.linearMap k A).comp aug.toLinearMap)
  have hD : ∀ a, D a = g (a - algebraMap k A (aug a)) := fun a => rfl
  have hsub : ∀ a, a - algebraMap k A (aug a) ∈ RingHom.ker aug := by
    intro a; simp [RingHom.mem_ker]
  have hDmul : ∀ a b, D (a * b) = aug a * D b + aug b * D a := by
    intro a b
    have e : a * b - algebraMap k A (aug (a * b)) =
        (a - algebraMap k A (aug a)) * (b - algebraMap k A (aug b))
          + aug a • (b - algebraMap k A (aug b)) + aug b • (a - algebraMap k A (aug a)) := by
      rw [map_mul, Algebra.smul_def, Algebra.smul_def, map_mul]; ring
    have h0 : g ((a - algebraMap k A (aug a)) * (b - algebraMap k A (aug b))) = 0 :=
      hgN _ (Ideal.mem_sup_left (by rw [pow_two]; exact Ideal.mul_mem_mul (hsub a) (hsub b)))
    rw [hD, hD, hD, e, map_add (f := _), map_add (f := _), h0, map_smul, map_smul, smul_eq_mul, smul_eq_mul, zero_add]
  let L : A →ₗ[k] DualNumber k :=
    (Algebra.linearMap k (DualNumber k)).comp aug.toLinearMap + (TrivSqZeroExt.inrHom k k).comp D
  have hLfst : ∀ a, (L a).fst = aug a := by intro a; simp [L, TrivSqZeroExt.algebraMap_eq_inl]
  have hLsnd : ∀ a, (L a).snd = D a := by intro a; simp [L, TrivSqZeroExt.algebraMap_eq_inl]
  let φ : A →ₐ[k] DualNumber k := AlgHom.ofLinearMap L
    (by ext <;> simp [hLfst, hLsnd, hD])
    (by intro a b; ext <;> simp [hLfst, hLsnd, hDmul] <;> ring)
  have hφ : ∀ a, φ a = L a := fun a => rfl
  refine ⟨φ, ?_, ?_, x, hxm, ?_⟩
  · ext a; simp [hφ, hLfst]
  · intro a ha
    ext
    · simp [hφ, hLfst]; exact hIm ha
    · simp only [hφ, hLsnd, TrivSqZeroExt.snd_zero]
      rw [hD]
      have : aug a = 0 := hIm ha
      rw [this, map_zero, sub_zero]
      exact hgN a (Ideal.mem_sup_right ha)
  · intro h0
    apply hf
    have := congrArg TrivSqZeroExt.snd h0
    rw [hφ, hLsnd, hD, TrivSqZeroExt.snd_zero, (RingHom.mem_ker).mp hxm, map_zero, sub_zero] at this
    exact this

end GlobalTheory.NotLeSqSup
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.KerJetAugEqSpanTorusUnionQuotient

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace JetGenerators

theorem exists_tangent {k A : Type} [Field k] [CommRing A] [Algebra k A] (aug : A →ₐ[k] k)
    {I : Ideal A} {n : ℕ} (hJ : (RingHom.ker aug) ^ (n + 1) = ⊥) (hI : I ≤ RingHom.ker aug)
    (hne : ¬ RingHom.ker aug ≤ I) :
    ∃ φ : A →ₐ[k] DualNumber k, (TrivSqZeroExt.fstHom k k k).comp φ = aug ∧ (∀ a ∈ I, φ a = 0) ∧
      ∃ a ∈ RingHom.ker aug, φ a ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.NotLeSqSup.main
  | exact _root_.GlobalTheory.NotLeSqSup.main
  | (apply _root_.GlobalTheory.NotLeSqSup.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NotLeSqSup.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NotLeSqSup.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NotLeSqSup.main ..)

theorem spMap_jetAug {k : Type} [CommRing k] {G : Over (Spec (CommRingCat.of k))} [GrpObj G] {d : ℕ}
    {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin d) m) ⟶ G} (hx : Chart.IsUnivChart G d x)
    (n : ℕ) {A : Type} [CommRing A] [Algebra k A] :
    Chart.spMap ((Algebra.ofId k A).comp (Chart.jetAug k (Fin d) n)) ≫ x n = 1 := by
  have : (Algebra.ofId k A).comp (Chart.jetAug k (Fin d) n) =
      ((Algebra.ofId k A).comp (Chart.jetAug k (Fin d) 0)).comp (Chart.jetZeroR k (Fin d) n) := by
    apply Chart.jet_ext
    intro j
    rfl
  rw [this, ← Chart.spMap_comp, Category.assoc, hx.2.1 n, MonObj.comp_one]

theorem eq_one_of_basis {S : Scheme.{0}} {X : Type} [AddCommGroup X] {κ : Type}
    (b : Module.Basis κ ℤ X) {Z : Over S} (y : Z ⟶ splitTorus S X)
    (h : ∀ j, y.left.appTop.hom (charUnit S X (b j)).val = 1) : y = 1 := by
  obtain ⟨e, he⟩ := exists_splitTorus_points_mulEquiv S X Z
  apply e.injective
  rw [map_one]
  have h1 : (MonoidHom.toAdditiveRight (e y)).toIntLinearMap = 0 := by
    apply b.ext
    intro j
    change Additive.ofMul (e y (Multiplicative.ofAdd (b j))) = Additive.ofMul 1
    congr 1
    exact Units.ext ((he y (b j)).trans (h j))
  refine MonoidHom.ext fun χ => ?_
  exact congrArg Additive.toMul (LinearMap.congr_fun h1 χ.toAdd)

end JetGenerators

theorem ker_jetAug_eq_span_torus_union_quotient :
    ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X] (r : ℕ) (b : Module.Basis (Fin r) ℤ X) (G B : Over (Spec (CommRingCat.of k))) [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus (Spec (CommRingCat.of k)) X ⟶ G), IsMonHom q → IsMonHom i → IsPullback i (toUnit _) q η[B] → ∀ (d g n : ℕ) (x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin d) m) ⟶ G) (xB : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin g) m) ⟶ B), Chart.IsUnivChart G d x → Chart.IsUnivChart B g xB → ∀ (ψ : (Chart.JetR k (Fin g) n) →ₐ[k] (Chart.JetR k (Fin d) n)), x n ≫ q = Chart.spMap ψ ≫ xB n → ∀ T : Fin r → (Chart.JetR k (Fin d) n), (∀ j, Chart.jetAug k (Fin d) n (T j) = 0) → (∀ (φ : (Chart.JetR k (Fin d) n) →ₐ[k] DualNumber k) (y : Chart.sp (R₀ := k) (DualNumber k) ⟶ splitTorus (Spec (CommRingCat.of k)) X), Chart.spMap φ ≫ x n = y ≫ i → ∀ j, (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom (1 + φ (T j)) = y.left.appTop.hom (charUnit (Spec (CommRingCat.of k)) X (b j)).val) → RingHom.ker (Chart.jetAug k (Fin d) n) = Ideal.span (Set.range T ∪ Set.range fun l => ψ (Chart.zR n l)) := by
  intro k _ X _ r b G B _ _ q i hq hi hpb d g n x xB hx hxB ψ hψ T hT hchar
  have hI : Ideal.span (Set.range T ∪ Set.range fun l => ψ (Chart.zR n l)) ≤
      RingHom.ker (Chart.jetAug k (Fin d) n) := by
    rw [Ideal.span_le]
    rintro _ (⟨j, rfl⟩ | ⟨l, rfl⟩)
    · exact hT j
    · have hz : IsNilpotent (Chart.zR (R := k) n l) := ⟨n + 1, by
        have := Ideal.pow_mem_pow (Chart.zR_mem_ker (R := k) n l) (n + 1)
        rwa [Chart.ker_jetAug_pow, Ideal.mem_bot] at this⟩
      exact ((hz.map ψ).map (Chart.jetAug k (Fin d) n)).eq_zero
  refine le_antisymm ?_ hI
  by_contra hne
  obtain ⟨φ, hφ1, hφ2, a, haJ, ha⟩ :=
    JetGenerators.exists_tangent _ (Chart.ker_jetAug_pow (R := k) (Fin d) n) hI hne
  have hn : n ≠ 0 := by
    rintro rfl
    have : RingHom.ker (Chart.jetAug k (Fin d) 0) = ⊥ :=
      (pow_one _).symm.trans (Chart.ker_jetAug_pow (R := k) (Fin d) 0)
    exact hne (this ▸ bot_le)
  have hφψ : φ.comp ψ = (Algebra.ofId k (DualNumber k)).comp (Chart.jetAug k (Fin g) n) := by
    apply Chart.jet_ext
    intro l
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Chart.jetAug_zR, map_zero]
    exact hφ2 _ (Ideal.subset_span (Or.inr ⟨l, rfl⟩))
  have hq1 : (Chart.spMap φ ≫ x n) ≫ q = toUnit _ ≫ η[B] := by
    rw [Category.assoc, hψ, ← Category.assoc, Chart.spMap_comp, hφψ, JetGenerators.spMap_jetAug hxB]
    rfl
  have hy := (hpb.lift_fst _ _ hq1).symm
  have hy1 : hpb.lift _ _ hq1 = 1 := by
    apply JetGenerators.eq_one_of_basis b
    intro j
    rw [← hchar φ _ hy j, hφ2 _ (Ideal.subset_span (Or.inl ⟨j, rfl⟩)), add_zero, map_one]
  rw [hy1, MonObj.one_comp] at hy
  have hker : (RingHom.ker (TrivSqZeroExt.fstHom k k k)) ^ (n + 1) = ⊥ := by
    rw [← le_bot_iff]
    refine (Ideal.pow_le_pow_right (show 2 ≤ n + 1 by omega)).trans ?_
    rw [pow_two, Ideal.mul_le]
    intro u hu v hv
    have hu' : u.fst = 0 := hu
    have hv' : v.fst = 0 := hv
    rw [Ideal.mem_bot]
    ext <;> simp [hu', hv']
  have huniq := (hx.2.2 (DualNumber k) (TrivSqZeroExt.fstHom k k k) n hker 1
    (MonObj.comp_one _)).unique (y₁ := φ)
    (y₂ := (Algebra.ofId k (DualNumber k)).comp (Chart.jetAug k (Fin d) n)) ⟨hφ1, hy.symm⟩
    ⟨by ext1 z; simp, (JetGenerators.spMap_jetAug hx n).symm⟩
  apply ha
  have h0 : Chart.jetAug k (Fin d) n a = 0 := haJ
  rw [huniq, AlgHom.comp_apply, h0, map_zero]

end GlobalTheory
end
end
