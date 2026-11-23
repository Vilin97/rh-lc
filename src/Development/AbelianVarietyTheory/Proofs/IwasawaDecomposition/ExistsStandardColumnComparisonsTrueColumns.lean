module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardFormComparisonSymmetricLevelMemberStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianColumnChoicesOfFormsLevelsClassesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianColumnsGeneratorsBaseLatticesFunctional
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianDataAtLevelPrimeStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPairMovedOfMultipliesLocalFunctional
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianColumnsGeneratorsBaseLatticesFunctionalStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitianColumns_generators_baseLattices_functionals : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → (∀ u (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((A u).piU : (I.rec7 l Z).host.E) → ∀ m : (H.lev0 u).fM w h, a • m = 0) → Formalism.L2.Herm.SymmetricCofactorCompatibility (I.rec7 l Z) H A ∧ Formalism.L2.Herm.SymmetricBaseCompatibility (I.rec7 l Z) H A ∧ Nonempty (Formalism.L2.Herm.SymmetricResidueFieldLevels (I.rec7 l Z) H A) ∧ ∃ X0 : Formalism.L2.Herm.SymmetricLevelZeroData (I.rec7 l Z) H A, ∀ u, (X0 u).piG = X.piG := by
  first | exact @GlobalTheory.Mem.Col2.TC.herm_rest_tied | exact GlobalTheory.Mem.Col2.TC.herm_rest_tied | (intros; apply GlobalTheory.Mem.Col2.TC.herm_rest_tied <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroHermitianLevelUniformiserKillsValues

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.LevTwist

section Re

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem reL_rfl {a : ℕ} (L : Submodule (𝓞 E) (Fin a → E)) : reL (rfl : a = a) L = L := by
  have e : ((reV (rfl : a = a) E : (Fin a → E) →ₗ[E] (Fin a → E)).restrictScalars (𝓞 E)) = LinearMap.id :=
    LinearMap.ext fun x => funext fun i => rfl
  rw [reL, e, Submodule.map_id]

theorem reGL_rfl {a : ℕ} (R : Type) [CommRing R] (g : GL (Fin a) R) : reGL (rfl : a = a) R g = g := by
  ext i j
  rfl




theorem fun_transport {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E) (J' : Matrix (Fin b) (Fin b) E)
    (hJ : J' = J.reindex (finCongr h) (finCongr h)) (Lb : Submodule (𝓞 E) (Fin a → E)) (Lb' : Submodule (𝓞 E) (Fin b → E))
    (hL : Lb' = reL h Lb) (v : HeightOneSpectrum (𝓞 F)) {M : Type} [AddCommGroup M] [Module (intV E v) M]
    (f' : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J' Lb')) →ₗ[intV E v] M) :
    ∃ f : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J Lb)) →ₗ[intV E v] M,
      (f' ≠ 0 → f ≠ 0) ∧ (∀ r : intV E v, (∀ x, f' (r • x) = 0) → ∀ x, f (r • x) = 0) ∧
      ((∀ x, x.1 ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb' → f' x = 0) →
        ∀ x, x.1 ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb → f x = 0) ∧
      ∀ (U : Subgroup (GL (Fin a) (E ⊗[F] v.adicCompletion F))) (U' : Subgroup (GL (Fin b) (E ⊗[F] v.adicCompletion F))),
        U' = U.map (reGL h _).toMonoidHom → U' = levelVL σ J' v Lb' ⊓ stabFun _ f' →
        U = levelVL σ J v Lb ⊓ stabFun _ f := by
  subst h
  obtain rfl : J' = J := by
    rw [hJ]; ext i j; rfl
  obtain rfl : Lb' = Lb := by rw [hL, reL_rfl]
  refine ⟨f', id, fun _ h => h, id, ?_⟩
  rintro U U' rfl h
  rw [← h]
  ext g
  simp only [Subgroup.mem_map]
  constructor
  · intro hg
    exact ⟨g, hg, reGL_rfl _ g⟩
  · rintro ⟨g', hg', e⟩
    have : g' = g := (reGL_rfl _ g').symm.trans e
    exact this ▸ hg'

end Re

section Pi

theorem smul_eq_zero_of_prime_card {S M : Type} [CommRing S] [AddCommGroup M] [Module S M] {p : ℕ} (hp : p.Prime)
    (hc : Nat.card M = p) (a : S) {m₀ : M} (h1 : m₀ ≠ 0) (h2 : a • m₀ = 0) (m : M) : a • m = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 (mem_zmultiples_of_prime_card hc h1 (g' := m))
  rw [smul_comm, h2, smul_zero]


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem pi_kills {D : D7} {u : D.what₂.Word} {A : AtTTied u} {i : ℕ} {hi : i ≤ D.R.m} (P : LvTied u A i hi) (K : ClsTied u i hi)
    (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) (hT : FvTie P K fMe) (v : (D.mem u).A.vT)
    (a : intV D.host.E (A.eV v).1)
    (ha : (a : D.host.E ⊗[D.host.F] (A.eV v).1.adicCompletion D.host.F) =
      inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) ((A.piU : 𝓞 D.host.E) : D.host.E))
    (m : K.lev.fM (A.eV v).1 (A.eV v).2) : a • m = 0 := by
  obtain ⟨c, -⟩ := K.y_bij.2 (Quotient.mk'' 1)
  obtain ⟨x, hx⟩ : ∃ x, (D.fm u).fv i v c x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact (D.fm u).fv_ne i v c (LinearMap.ext hc)
  obtain ⟨z, rfl⟩ := P.pr_surj v c x
  have hin : ∀ z : ↥(Ld D u i hi c), ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
      (fun a => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z.1 a)) ∈
      latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb)) :=
    fun z => (GlobalTheory.LevelHecke.MovePair.ld_loc K _ c _).1 (Submodule.subset_span ⟨z.1, z.2, rfl⟩)
  have h1 : K.lev.fT _ (A.eV v).2 ⟨_, hin z⟩ ≠ 0 := by
    intro h0
    apply hx
    rw [hT v c z (hin z), h0, map_zero]
  have h3 : K.lev.fT _ (A.eV v).2 ⟨_, hin (A.piU • z)⟩ = 0 := by
    have hz0 : (D.fm u).fv i v c (P.pr v c (A.piU • z)) = 0 := by
      rw [P.pr_smul, A.res_pi, zero_smul, map_zero]
    exact (fMe v).injective (((hT v c _ (hin _)).symm.trans hz0).trans (map_zero (fMe v)).symm)
  have e : a • (⟨_, hin z⟩ : latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1)
      (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb))) =
      ⟨_, hin (A.piU • z)⟩ := by
    apply Subtype.ext
    have e1 : (fun b => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) ((A.piU • z).1 b)) =
        (a : D.host.E ⊗[D.host.F] (A.eV v).1.adicCompletion D.host.F) •
          fun b => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z.1 b) := by
      funext b
      rw [ha]
      show inclE (F := D.host.F) _ (((A.piU : 𝓞 D.host.E) : D.host.E) * z.1 b) = _
      rw [map_mul]
      rfl
    show (a : D.host.E ⊗[D.host.F] (A.eV v).1.adicCompletion D.host.F) •
        (((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
          (fun b => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z.1 b))) =
        ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
          (fun b => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) ((A.piU • z).1 b))
    rw [e1, Matrix.mulVec_smul]
  have h2 : a • K.lev.fT _ (A.eV v).2 ⟨_, hin z⟩ = 0 :=
    (map_smul (K.lev.fT _ (A.eV v).2) a _).symm.trans ((congrArg (K.lev.fT _ (A.eV v).2) e).trans h3)
  exact smul_eq_zero_of_prime_card (D.mem u).A.T_prime (K.lev.fM_card _ _) a h1 h2 m

end Pi

section Main




theorem stepZeroHermitianLevel_with_formsFunctional (D : D7) (u : D.what₂.Word) {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (F : FormsTiedSym D u Ch chOf)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (hS : SameCar (rank_eq_first_level D.R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb L.Uloc
      (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U
      (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1)
      (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1)) :
    ∃ L' : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u),
      L'.Lb = L.Lb ∧ L'.Uloc = L.Uloc ∧ L'.U = L.U ∧ L'.y = L.y ∧ L'.stabI = L.stabI ∧ L'.splitG = L.splitG ∧ L'.frG = L.frG ∧
      ∀ (w : HeightOneSpectrum (𝓞 D.host.F)) (h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal)
        (a : intV D.host.E w),
        (a : TensorProduct D.host.F D.host.E (w.adicCompletion D.host.F)) =
          inclE (F := D.host.F) (w.adicCompletion D.host.F) ((F.atT.piU : 𝓞 D.host.E) : D.host.E) →
        ∀ m : L'.fM w h, a • m = 0 := by
  have hJ : gramN D 0 (Nat.zero_le _) =
      (D.sp.gram0).reindex (finCongr (rank_eq_first_level D.R)) (finCongr (rank_eq_first_level D.R)) := by
    ext i j
    rfl
  have key := fun (w : HeightOneSpectrum (𝓞 D.host.F)) (h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal) =>
    fun_transport (rank_eq_first_level D.R) (sigD D) D.sp.gram0 (gramN D 0 (Nat.zero_le _)) hJ L.Lb
      (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb hS.Lb_eq w
      ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT w h)
  choose fT' k1 k2 k3 k4 using key
  refine ⟨{ L with
    fM := (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fM
    fM_acg := (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fM_acg
    fM_mod := (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fM_mod
    fT := fT'
    fT_ne := fun v h => k1 v h ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT_ne v h)
    fT_T := fun v h => k2 v h _ ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT_T v h)
    fM_card := (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fM_card
    fT_L := fun v h => k3 v h ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT_L v h)
    UlocAlt := fun v h => k4 v h _ _ (hS.Uloc_eq v) ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.UlocAlt v h) },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro w h a ha m
  obtain ⟨v, hv⟩ := F.atT.eV.surjective ⟨w, h⟩
  have hw : (F.atT.eV v).1 = w := congrArg Subtype.val hv
  subst hw
  exact pi_kills (F.lv 0 (Nat.zero_le _)) (F.cls 0 (Nat.zero_le _) (Or.inl rfl))
    (F.fMe 0 (Nat.zero_le _) (Or.inl rfl)) (F.fv 0 (Nat.zero_le _) (Or.inl rfl)) v a ha m

end Main




theorem stepZeroHermitianLevel_uniformiser_kills_values : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (L : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u)), SameCar (rank_eq_first_level (I.rec7 l Z).R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb L.Uloc (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1) (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1) → ∃ L' : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u), L'.Lb = L.Lb ∧ L'.Uloc = L.Uloc ∧ L'.U = L.U ∧ L'.y = L.y ∧ L'.stabI = L.stabI ∧ L'.splitG = L.splitG ∧ L'.frG = L.frG ∧ ∀ (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) → ∀ m : L'.fM w h, a • m = 0 :=
  by
  intro B X I _ _ l Z u Ch chOf F _ L hS
  exact stepZeroHermitianLevel_with_formsFunctional (I.rec7 l Z) u F L hS

end GlobalTheory.Mem.Col2.LevTwist

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroHermitianLevelUniformiserKillsValuesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.stepZeroHermitianLevel_uniformiser_kills_values_alt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (L : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u)), SameCar (rank_eq_first_level (I.rec7 l Z).R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb L.Uloc (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1) (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1) → ∃ L' : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u), L'.Lb = L.Lb ∧ L'.Uloc = L.Uloc ∧ L'.U = L.U ∧ L'.y = L.y ∧ L'.stabI = L.stabI ∧ L'.splitG = L.splitG ∧ L'.frG = L.frG ∧ ∀ (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) → ∀ m : L'.fM w h, a • m = 0 := by
  first | exact @GlobalTheory.Mem.Col2.LevTwist.stepZeroHermitianLevel_uniformiser_kills_values | exact GlobalTheory.Mem.Col2.LevTwist.stepZeroHermitianLevel_uniformiser_kills_values | (intros; apply GlobalTheory.Mem.Col2.LevTwist.stepZeroHermitianLevel_uniformiser_kills_values <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardColumnComparisonsTrueColumns

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC



theorem colsTiedSym_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∃ C : ColsTiedSym (I.rec7 l Z), I.StdC l Z C ∧ ∀ u, I.StdLvC l Z u (C.forms u) := by
  intro B X I hOk hP l Z
  obtain ⟨Ch, chOf, F, hF, hfin, hm, hgl, hchi⟩ := GlobalTheory.T.exists_standardFormComparison_symmetricLevel_members I hOk hP l Z
  obtain ⟨lev00, lev, cls, vT, Fv, hH0⟩ := GlobalTheory.T.hermitianColumnChoices_of_formsLevelsClasses I hOk hP l Z Ch chOf F hfin hm (fun u => (hF u).1)
  choose lev0 hLb hUl hU hy hst hsp hfrG hpi using fun u => GlobalTheory.T.stepZeroHermitianLevel_uniformiser_kills_values_alt I hOk hP l Z u (F u) (hF u).1 (lev00 u) (hH0.car0 u)
  let H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z) :=
    { lev0 := lev0, Ch := Ch, ChFin := hfin, Ch_m := hm, chOf := chOf, lev := lev, cls := cls, vT := vT, Fv := Fv }
  have hH : CarH H F :=
    { eV := hH0.eV, fv := hH0.fv
      car0 := fun u => by
        show SameCar _ (lev0 u).Lb _ (lev0 u).Uloc _ (lev0 u).U _ (fun c => ((lev0 u).y c).1) _ (fun c s => ((lev0 u).stabI c s).1) _
        rw [hLb u, hUl u, hU u, hy u, hst u]; exact hH0.car0 u
      carC := hH0.carC, carM := hH0.carM
      sp := fun u => by show _ = (lev0 u).splitG; rw [hsp u]; exact hH0.sp u
      fr0 := fun u => by show ∀ i v h, _ = reGL _ _ ((lev0 u).frG i v h); rw [hfrG u]; exact hH0.fr0 u }
  obtain ⟨A, hT, hAd, hSt⟩ := GlobalTheory.T.exists_hermitian_data_carT_of_std I hOk hP l Z H F hF hH
  obtain ⟨hCof, hBase, ⟨hFv⟩, X0, hX0⟩ := GlobalTheory.T.hermitianColumns_generators_baseLattices_functionals I hOk hP l Z H F A hF hH hT
    (fun u w h a ha m => hpi u w h a (by rw [ha, hT.piU u]) m)
  have hStd := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hP l Z).1
  have hpiG : ∀ u u', (X0 u).piG = (X0 u').piG := fun u u' => by rw [hX0 u, hX0 u']
  have hpiG' : ∀ u, (F u).gl.piG = (X0 u).piG := fun u => by rw [hX0 u]; exact ((hF u).1.gl).piG
  have hfr0 : ∀ u u', (F u).glev0.fr = (F u').glev0.fr := fun u u' => by
    funext j v h
    rw [(hF u).1.fr0, (hF u').1.fr0]
  have hfrP : ∀ u u', (F u).glevP.fr = (F u').glevP.fr := fun u u' => by
    funext j v h
    rw [(hF u).1.frP, (hF u').1.frP]
  refine ⟨
    { herm :=
        { base := H, atT := A, levelZeroCompatibility := X0, ad := hAd, cof := hCof, piG := hpiG,
          stabMap := hSt, fvI := hFv, std := hStd, baseL := hBase }
      forms := F
      eV := hH.eV
      piU := hT.piU
      res := hT.res
      car0 := hH.car0
      carC := hH.carC
      carM := hH.carM
      carP := hT.carP
      lattice₂ := hT.lattice₂
      pr := hT.pr
      prk := hT.prk
      prC := hT.prC
      z0 := hT.z0
      ga := hT.ga
      sp := hH.sp
      piG := hpiG'
      fr0 := hH.fr0
      gl_const := hgl
      chi := hchi
      frame_level_zero_const := hfr0
      frP_const := hfrP }, fun u => (hF u).1, fun u => (hF u).2⟩

end GlobalTheory.Mem.Col2.TC
end
end
