module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenLocusTorsionPointsAreLevelSectionsStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionSectionsOfRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBundleLevelOdd
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionsExactKernelLocusOpen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LevTrivOpen

variable {S : Scheme.{0}}

theorem range_subset_iff_mem {k : Type} [Field k] (x : Sp k ⟶ S) (U : Set S) (p : Sp k) :
    Set.range x.base ⊆ U ↔ x.base p ∈ U := by
  refine ⟨fun h => h ⟨p, rfl⟩, ?_⟩
  rintro h _ ⟨q, rfl⟩
  rwa [Subsingleton.elim q p]

theorem pow_nsmul {G : Over S} [GrpObj G] {h : ℕ} (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G))
    (hadd : ∀ a b, lev (a + b) = lev a * lev b) (n : ℕ) (c : Fin h ⊕ Fin h → ℤ) : lev (n • c) = lev c ^ n := by
  have h0 : lev 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

end GlobalTheory.LevTrivOpen

open GlobalTheory.LevCover GlobalTheory.LevTrivOpen in
theorem GlobalTheory.levTriv_locus_open : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → 3 ≤ M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S), (∀ a, (toUnit (Over.mk x₀) ≫ lev a = 1 ↔ ∃ b, a = M • b)) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), Set.range x.base ⊆ W → ∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M • b) := by
  intro S _ M t G _ _ h lev hab hM hadd hpow k _ _ x₀ hx₀
  have hu : IsUnit (M : Γ(S, ⊤)) := by
    have := (GlobalTheory.SiegelTor.isUnit_natCast (n := M) (by omega)).map
      (t.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (GlobalTheory.SiegelTor.cycAway M))).inv.hom)
    rwa [map_natCast] at this
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion G (hG := hab) hu
  have hU : ∀ f : 𝟙_ (Over S) ⟶ G, ∃ U : S.Opens, IsClosed (U : Set S) ∧ (f ^ M = 1 → ∀ (k' : Type) [Field k']
      [IsAlgClosed k'] (x : Sp k' ⟶ S), (toUnit (Over.mk x) ≫ f = 1 ↔ Set.range x.base ⊆ U)) := fun f => by
    by_cases hf : f ^ M = 1
    · obtain ⟨U, hUc, HU⟩ := GlobalTheory.TorsionSections.clopenCond_torsion_eq (n := M) (T := 𝟙_ (Over S)) hf (one_pow M)
      refine ⟨U, hUc, fun _ k' _ _ x => ?_⟩
      have := HU (Over.mk x) (toUnit (Over.mk x))
      simp only [MonObj.comp_one] at this
      simpa using this
    · exact ⟨⊤, isClosed_univ, fun h => absurd h hf⟩
  choose Uf hUc HU using hU
  classical
  obtain ⟨κ, _, q, hq⟩ := exists_finite_mod (Fin h ⊕ Fin h → ℤ) (show 0 < M by omega)
  let P : (Fin h ⊕ Fin h → ℤ) → Prop := fun a => ∃ b, a = M • b
  let A : (Fin h ⊕ Fin h → ℤ) → Set S := fun a => {s | s ∈ (Uf (lev a) : Set S) ↔ P a}
  have hAo : ∀ a, IsOpen (A a) := fun a => by
    by_cases hp : P a
    · convert (Uf (lev a)).isOpen using 1
      ext s
      simp only [A, Set.mem_setOf_eq, hp, iff_true, SetLike.mem_coe]
    · convert (hUc (lev a)).isOpen_compl using 1
      ext s
      simp only [A, Set.mem_setOf_eq, hp, iff_false, Set.mem_compl_iff, SetLike.mem_coe]
  have hAq : ∀ a a', q a = q a' → A a = A a' := fun a a' e => by
    obtain ⟨c, rfl⟩ := hq a a' e
    have hl : lev (a + M • c) = lev a := by rw [hadd, pow_nsmul lev hadd, hpow, _root_.mul_one]
    have hP : P (a + M • c) ↔ P a :=
      ⟨fun ⟨b, hb⟩ => ⟨b - c, by rw [smul_sub, ← hb]; abel⟩, fun ⟨b, hb⟩ => ⟨b + c, by rw [hb, smul_add]⟩⟩
    ext s
    simp only [A, Set.mem_setOf_eq, hl, hP]
  let pick : κ → (Fin h ⊕ Fin h → ℤ) := fun c => if hc : ∃ a, q a = c then hc.choose else 0
  have hpick : ∀ a, A a = A (pick (q a)) := fun a => by
    have hc : ∃ a', q a' = q a := ⟨a, rfl⟩
    refine hAq _ _ ?_
    simp only [pick, dif_pos hc]
    exact hc.choose_spec.symm
  refine ⟨⟨⋂ c, A (pick c), isOpen_iInter_of_finite fun c => hAo _⟩, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩
    simp only [TopologicalSpace.Opens.coe_mk, Set.mem_iInter]
    intro c
    show x₀.base p ∈ (Uf (lev (pick c)) : Set S) ↔ P (pick c)
    rw [← range_subset_iff_mem, ← HU _ (hpow _) k x₀]
    exact hx₀ _
  · intro k' _ _ x hx a
    obtain ⟨p⟩ := (inferInstance : Nonempty (Sp k'))
    have h1 := hx ⟨p, rfl⟩
    simp only [TopologicalSpace.Opens.coe_mk, Set.mem_iInter] at h1
    have h2 : x.base p ∈ A a := by rw [hpick]; exact h1 _
    rw [HU _ (hpow a) k' x, range_subset_iff_mem _ _ p]
    exact h2
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionsExactKernelLocusOpenStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.level_sections_exact_kernel_locus_open : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → 3 ≤ M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S), (∀ a, (toUnit (Over.mk x₀) ≫ lev a = 1 ↔ ∃ b, a = M • b)) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), Set.range x.base ⊆ W → ∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M • b) := by
  first | (exact @GlobalTheory.levTriv_locus_open) | (exact GlobalTheory.levTriv_locus_open) | (intros; apply GlobalTheory.levTriv_locus_open  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SympAtPullbackIff

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.SympLevLocus

def SympAt {S : Scheme.{0}} {A : Over S} [GrpObj A] (P : LB (G2 A).left) (h M : ℕ)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) (k : Type) [Field k] (x : Sp k ⟶ S) (z : kˣ) : Prop :=
  (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M • b)) ∧
    (∀ g : Over.mk x ⟶ A, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g) ∧
    ∀ a b, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) M (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b)
      (unitOn (z ^ (2 * omegaStd a b)))

theorem isSympLev_iff {S : Scheme.{0}} {A : Over S} [GrpObj A] (P : LB (G2 A).left) (h M : ℕ) {B : Type}
    [CommRing B] (ζ : B) (t₁ : S ⟶ Sp B) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) :
    IsSympLev P h M ζ t₁ lev ↔ (∀ a b, lev (a + b) = lev a * lev b) ∧ (∀ a, lev a ^ M = 1) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k) (z : kˣ), x ≫ t₁ = spMap β →
        (z : k) = β ζ → SympAt P h M lev k x z :=
  Iff.rfl

end GlobalTheory.SympLevLocus

namespace GlobalTheory.SympLevLocus


open GlobalTheory.SiegelPull in
theorem sympAt_pullback_iff {S T : Scheme.{0}} (g : T ⟶ S) {A : Over S} [GrpObj A] [IsCommMonObj A] {A' : Over T}
    [GrpObj A'] [IsCommMonObj A'] {P : LB (G2 A).left} {P' : LB (G2 A').left} {φ : A'.left ⟶ A.left}
    {φ₂ : (G2 A').left ⟶ (G2 A).left} {h M : ℕ} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)}
    {lev' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ A')} (hP : P.IsLB) (hP' : P'.IsLB)
    (pb : IsGrpPullback A' A g φ) (sq : IsSquare φ φ₂) (iso : LBIso P' (P.pull φ₂))
    (hl : ∀ a, (lev' a).left ≫ φ = g ≫ (lev a).left) (k : Type) [Field k] (x : Sp k ⟶ T) (z : kˣ) :
    SympAt P' h M lev' k x z ↔ SympAt P h M lev k (x ≫ g) z := by
  have push : ∀ a, pushHom pb (Over.mk x) (toUnit (Over.mk x) ≫ lev' a) = toUnit (Over.mk (x ≫ g)) ≫ lev a := by
    intro a
    apply Over.OverMorphism.ext
    show ((toUnit (Over.mk x)).left ≫ (lev' a).left) ≫ φ = (toUnit (Over.mk (x ≫ g))).left ≫ (lev a).left
    rw [Category.assoc, hl, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
    rfl
  have inj := push_injective pb (Over.mk x)
  have surj := push_surjective pb (Over.mk x)
  refine and_congr (forall_congr' fun a => ?_) (and_congr ⟨fun H g₀ hg₀ => ?_, fun H g₀ hg₀ => ?_⟩
    (forall_congr' fun a => forall_congr' fun b => ?_))
  · rw [← inj.eq_iff, push, map_one]
  · obtain ⟨g₁, rfl⟩ := surj g₀
    obtain ⟨a, ha⟩ := H g₁ (inj (by rw [map_pow, map_one]; exact hg₀))
    exact ⟨a, (push a).symm.trans (congrArg _ ha)⟩
  · obtain ⟨a, ha⟩ := H (pushHom pb (Over.mk x) g₀) (by rw [← map_pow, hg₀, map_one])
    exact ⟨a, inj ((push a).trans ha)⟩
  · exact weilIs_grpPullback_of_comm S T A A' g φ _ _ (pull_isLB hP _) (pull_isLB hP' _) pb
      (diag_iso sq iso) (Over.mk x) M _ _ _ _ _
      (congrArg (fun q => q.left) (push a).symm) (congrArg (fun q => q.left) (push b).symm)

end GlobalTheory.SympLevLocus
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSymplecticLevelLocus

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.SympLevLocus

theorem range_sub_iff {X : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ X) (W : Set X) (p₀ : Sp k) :
    Set.range x.base ⊆ W ↔ x.base p₀ ∈ W := by
  refine ⟨fun H => H ⟨p₀, rfl⟩, ?_⟩
  rintro H _ ⟨p, rfl⟩
  rwa [Subsingleton.elim p p₀]


open GlobalTheory.SiegelPull in
theorem exists_open_sympLev : ∀ (h M : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ G)), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → 3 ≤ M → Odd M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → IsSympLev (P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)) h M (zetaAway M) (V.ι ≫ t) (fun a => GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback V.ι G) (lev a))) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)) (φ : c'.A.left ⟶ G.left) (φ₂ : (G2 c'.A).left ⟶ (G2 G).left), IsGrpPullback c'.A G g φ → IsSquare φ φ₂ → LBIso c'.P (P.pull φ₂) → (∀ a, (c'.lev a).left ≫ φ = g ≫ (lev a).left) → Set.range g.base ⊆ (U : Set S') := by
  intro h M S' _ t G _ _ P lev hab hP hr₁ hr₂ hsy hM hodd hadd htor
  let Good : S'.Opens → Prop := fun W => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S')
    (β : cycAway M →+* k) (z : kˣ), Set.range x.base ⊆ W → x ≫ t = spMap β → (z : k) = β (zetaAway M) →
      SympAt P h M lev k x z
  have hsup : ∀ (k : Type) [Field k] (x : Sp k ⟶ S'), Set.range x.base ⊆ (sSup {W | Good W} : S'.Opens) →
      ∃ W, Good W ∧ Set.range x.base ⊆ W := by
    intro k _ x hx
    let p₀ : Sp k := (⊥ : PrimeSpectrum k)
    rw [range_sub_iff x _ p₀] at hx
    obtain ⟨W, hW, hpW⟩ := TopologicalSpace.Opens.mem_sSup.1 hx
    exact ⟨W, hW, (range_sub_iff x _ p₀).2 hpW⟩
  refine ⟨sSup {W | Good W}, fun V hV => ?_, ?_⟩
  · have pb := Pdiv.PullbackComparison.isGrpPullback V.ι G
    refine (isSympLev_iff _ _ _ _ _ _).2 ⟨fun a b => push_injective pb _ ?_, fun a => push_injective pb _ ?_,
      fun k _ _ x β z hx hz => ?_⟩
    · rw [map_mul, push_secPull', push_secPull', push_secPull', hadd, MonObj.comp_mul]
    · rw [map_pow, map_one, push_secPull', ← MonObj.comp_pow, htor, MonObj.comp_one]
    · rw [sympAt_pullback_iff V.ι hP (pull_isLB hP _) pb (Pdiv.PullbackComparison.isSquare V.ι G)
        (Pdiv.PullbackComparison.gen_refl _ (pull_isLB hP _)) (fun a => secPull_left pb _)]
      obtain ⟨W, hW, hxW⟩ := hsup k (x ≫ V.ι) (by
        rintro _ ⟨p, rfl⟩
        exact hV (by first | exact (x.base p).2 | simp | (rw [← Scheme.Opens.range_ι V]; exact ⟨_, rfl⟩)))
      exact hW k (x ≫ V.ι) β z hxW (by rw [Category.assoc]; exact hx) hz
  · intro T g c' φ φ₂ pb sq iso hl
    rintro _ ⟨τ, rfl⟩
    obtain ⟨K, _, _, x₀, ⟨q, hq⟩⟩ := GlobalTheory.SiegelTypings.exists_geomPt τ
    obtain ⟨β, hβ⟩ := (⟨(Spec.preimage (x₀ ≫ g ≫ t)).hom, by simp [spMap]⟩ : ∃ β : cycAway M →+* K, spMap β = x₀ ≫ g ≫ t)
    let z : Kˣ := ((GlobalTheory.LowChart.isUnit_zetaAway M hM).map β).unit
    have hc : SympAt c'.P h M c'.lev K x₀ z := c'.geom K x₀ β z hβ.symm rfl
    obtain ⟨hS₁, hS₂, hS₃⟩ := (sympAt_pullback_iff g hP c'.isLB pb sq iso hl K x₀ z).1 hc
    have e₁ := GlobalTheory.T.level_sections_exact_kernel_locus_open S' M t G h lev hab hM hadd htor K (x₀ ≫ g)
    have e₂ := GlobalTheory.T.exists_open_locus_torsion_points_are_level_sections S' M t G h lev hab hM hadd htor K (x₀ ≫ g)
    have e₃ := GlobalTheory.T.symmetric_bundle_level_odd S' M t G P h lev hab hP hr₁ hr₂ hsy hM hodd hadd htor K (x₀ ≫ g) β z (by rw [Category.assoc, hβ]) rfl
    obtain ⟨W₁, hW₁, H₁⟩ := e₁ hS₁
    obtain ⟨W₂, hW₂, H₂⟩ := e₂ hS₂
    obtain ⟨W₃, hW₃, H₃⟩ := e₃ hS₃
    have hgood : Good (W₁ ⊓ W₂ ⊓ W₃) := fun k _ _ x β' z' hx hxt hz' =>
      ⟨H₁ k x (hx.trans (le_trans inf_le_left inf_le_left)), H₂ k x (hx.trans (le_trans inf_le_left inf_le_right)),
        H₃ k x β' z' (hx.trans inf_le_right) hxt hz'⟩
    have hmem : g.base τ ∈ (W₁ ⊓ W₂ ⊓ W₃ : S'.Opens) := by
      have e : (x₀ ≫ g).base q = g.base τ := by first | simp [← hq] | (rw [Scheme.Hom.comp_apply, hq]) | (rw [Scheme.comp_base_apply, hq])
      rw [← e]
      exact ⟨⟨hW₁ ⟨q, rfl⟩, hW₂ ⟨q, rfl⟩⟩, hW₃ ⟨q, rfl⟩⟩
    exact (le_sSup (show W₁ ⊓ W₂ ⊓ W₃ ∈ {W | Good W} from hgood)) hmem

end GlobalTheory.SympLevLocus
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSymplecticLevelLocusStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.isOpen_symplecticLevel_locus : ∀ (h M : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ G)), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → 3 ≤ M → Odd M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → IsSympLev (P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)) h M (zetaAway M) (V.ι ≫ t) (fun a => GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback V.ι G) (lev a))) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)) (φ : c'.A.left ⟶ G.left) (φ₂ : (G2 c'.A).left ⟶ (G2 G).left), IsGrpPullback c'.A G g φ → IsSquare φ φ₂ → LBIso c'.P (P.pull φ₂) → (∀ a, (c'.lev a).left ≫ φ = g ≫ (lev a).left) → Set.range g.base ⊆ (U : Set S') := by
  first | (exact @GlobalTheory.SympLevLocus.exists_open_sympLev) | (exact GlobalTheory.SympLevLocus.exists_open_sympLev) | (intros; apply GlobalTheory.SympLevLocus.exists_open_sympLev  <;> assumption)
end
end
