module

public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.Jets.SurjectiveAppTopSqCube
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIndexOfLocal
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsUniqueNormPrim
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RosIdSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPref
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ValSerGermFnVal
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsLawOfOfMatch
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TruncationFramesLocalSeries
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalJetsReindexFin
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValCongr
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffEv
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionValueZero
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.GsSpMapGermAt

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LinkSec

theorem comp_psum_two {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (s : T ⟶ T') (x₀ x₁ : T' ⟶ G)
    (I : Finset (Fin 2)) : s.left ≫ (psum G ![x₀, x₁] I).left = (psum G ![s ≫ x₀, s ≫ x₁] I).left := by
  have e : s ≫ psum G ![x₀, x₁] I = psum G ![s ≫ x₀, s ≫ x₁] I := by
    fin_cases I
    · exact MonObj.comp_one _
    · exact MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_one _))
    · exact MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_one _))
    · exact MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·)
        (MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_one _))))
  exact congrArg CommaMorphism.left e

theorem psum_mem {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] (w : G ⟶ G) (x : T ⟶ G)
    (I : Finset (Fin 2)) : ∃ k, (psum G ![x, x ≫ w] I).left = x.left ≫ JetSer.primφ w k := by
  have e₁ : x ≫ (𝟙 G * w) = x * (x ≫ w) := (MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id])
  have e₄ : x ≫ (1 : G ⟶ G) = 1 := MonObj.comp_one _
  have p₀ : psum G ![x, x ≫ w] ∅ = 1 := rfl
  have p₁ : psum G ![x, x ≫ w] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, x ≫ w] {1} = x ≫ w := _root_.mul_one _
  have p₄ : psum G ![x, x ≫ w] {0, 1} = x * (x ≫ w) := congrArg (x * ·) (_root_.mul_one _)
  have hI : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by revert I; decide
  rcases hI with rfl | rfl | rfl | rfl
  · exact ⟨4, congrArg CommaMorphism.left (p₀.trans e₄.symm)⟩
  · exact ⟨0, (congrArg CommaMorphism.left p₁).trans (Category.comp_id _).symm⟩
  · exact ⟨3, congrArg CommaMorphism.left p₂⟩
  · exact ⟨1, congrArg CommaMorphism.left (p₄.trans e₁.symm)⟩

theorem change_index {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (w : G ⟶ G)
    (x : T ⟶ G) (s : T ⟶ T') (x₀ x₁ : T' ⟶ G) (h₀ : s ≫ x₀ = x) (h₁ : s ≫ x₁ = x ≫ w)
    (e : LB.Gen (LB.LinComb L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![x₀, x₁] I.down).left) (cε 2)))
    (he : e.IsGen) (ρ : LB.Gen (LB.LinComb L (JetSer.primφ w) JetSer.primε)) (hρ : ρ.IsGen) (q : ℕ) (σ : H0 L q)
    (j : L.ι) (y : T.left) (hj : x.left y ∈ LB.wchart L (JetSer.primφ w) (fun _ => j)) (J) (hJ : Good L y J) :
    s.left y ∈ LB.wchart L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![x₀, x₁] I.down).left) (fun _ => j) ∧
    ∃ c : (T.left.presheaf.stalk y)ˣ,
      sval σ x.left y J = (c ^ q).val * gs x.left y _ (σ.f fun _ => j) ∧
      val ρ x.left y J * val e s.left y J =
        c * (gm x.left y _ (ρ.s fun _ => j) * gm s.left y _ (e.s fun _ => j)) := by
  have E : ∀ I : Finset (Fin 2), s.left ≫ (psum G ![x₀, x₁] I).left = (psum G ![x, x ≫ w] I).left := fun I => by
    rw [comp_psum_two, h₀, h₁]
  have hs : s.left y ∈ LB.wchart L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![x₀, x₁] I.down).left)
      (fun _ => j) := Set.mem_iInter.2 fun I => by
    obtain ⟨k, hk⟩ := psum_mem w x I.down
    have a : (x.left ≫ JetSer.primφ w k) y ∈ L.U j := Set.mem_iInter.1 hj k
    rw [← hk, ← E] at a
    exact a
  have hx : x.left y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j) :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hj 0
  let h : (T.left ⟶ G.left) → (T.left.presheaf.stalk y)ˣ := fun ψ => gm ψ y (L.U (J ψ) ⊓ L.U j) (L.g (J ψ) j)
  refine ⟨hs, h x.left, ?_, ?_⟩
  · refine (sec_trans σ x.left y (hJ.mem _ _) hx).trans (congrArg (· * _) (congrArg Units.val ?_))
    show ∏ _k : Fin 1, h (x.left ≫ 𝟙 _) ^ (q : ℤ) = _
    rw [Fintype.prod_unique, Category.comp_id, zpow_natCast]
  · have a : val ρ x.left y J = (∏ k, h (x.left ≫ JetSer.primφ w k) ^ JetSer.primε k) *
        gm x.left y _ (ρ.s fun _ => j) := gen_trans hρ x.left y (hJ.mem _ _) hj
    have b : val e s.left y J = (∏ I : ULift.{0} (Finset (Fin 2)),
        h (s.left ≫ (psum G ![x₀, x₁] I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card))) *
        gm s.left y _ (e.s fun _ => j) := gen_trans he s.left y (hJ.mem _ _) hs
    simp only [E] at b
    rw [a, b, JetSer.prod_prim, JetSer.prod_lam, _root_.mul_mul_mul_comm]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

def germAt (A : Type) [CommRing A] (y : Sp A) : A →+* (Sp A).presheaf.stalk y :=
  ((Sp A).presheaf.germ ⊤ y trivial).hom.comp (toΓ A)

theorem gs_toΓ_eq {A : Type} [CommRing A] (y : Sp A) (a : A) : gs (𝟙 _) y ⊤ (toΓ A a) = germAt A y a :=
  gs_eq (𝟙 _) y ⊤ trivial _

theorem gs_spMap_germAt {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (y : Sp B) (a : A) :
    gs (Geo.Tor.spMap f) y ⊤ (toΓ A a) = germAt B y (f a) := by
  have e := gs_pull (𝟙 _) (Geo.Tor.spMap f) y ⊤ trivial (toΓ A a)
  rw [Category.id_comp] at e
  refine e.symm.trans (Eq.trans ?_ (gs_toΓ_eq y _))
  exact congrArg (gs (𝟙 _) y ⊤)
    (congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

variable {V : Type} [CommRing V]

theorem psJet_pow {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ V) (q : ℕ) :
    psJet m (f ^ q) = psJet m f ^ q := by
  induction q with
  | zero => rw [pow_zero, pow_zero, FBIdJet.psJet_one]
  | succ q ih => rw [pow_succ, pow_succ, FBIdJet.psJet_mul, ih]

theorem toJet_eq {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ V) :
    JetSer.toJet m f = psJet m f := (congrArg (Ideal.Quotient.mk _) (FBIdJet.psTrunc_eq m f)).symm

theorem ev_pt_one {d : ℕ} (f : PS V 1 d) : ev (n := 1) ![pt V (n := 1) d 0] f = f := by
  have : (![pt V d 0] : Fin 1 → Pt V 1 d) = fun j => pt V d j := by
    funext j; fin_cases j; rfl
  rw [this]
  unfold ev
  exact congrFun MvPowerSeries.subst_self f

theorem gs_of_isSer1 {G : Over (Sp V)} {d : ℕ} (xT : JetPts G (Fin 1 × Fin d)) (x : JetSer.Fam G (Fin d))
    (hM : Match (oneCol d) xT x) (U : G.left.Opens) (f : Γ(G.left, U)) (g : PS V 1 d) (h : JetSer.IsSer1 x U f g)
    (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) :
    (xT m).left y ∈ U ∧ gs (xT m).left y U f = germAt _ y (psJet m g) := by
  have R : JetSer.Rep x (pt V (n := 1) d 0) (fun m => LinkLaw.toAt (V := V) (Jet V (Fin 1 × Fin d) m) ≫ xT m) := by
    refine ⟨fun j => by simp [pt], fun m => ?_⟩
    obtain ⟨e, he1, he2⟩ := hM m
    refine ⟨(e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m), fun j => ?_, ?_⟩
    · exact (he1 j).trans (JetSer.toJet_X m ((0 : Fin 1), j)).symm
    · apply Over.OverMorphism.ext
      exact (Category.id_comp _).trans he2
  obtain ⟨h1, h2⟩ := h 1 _ _ R m
  have e : (LinkLaw.toAt (V := V) (Jet V (Fin 1 × Fin d) m) ≫ xT m).left = (xT m).left := Category.id_comp _
  have h1' : ⊤ ≤ (xT m).left ⁻¹ᵁ U := e ▸ h1
  have h2' : JetSer.fnVal (A := Jet V (Fin 1 × Fin d) m) (xT m).left U f = psJet m g :=
    (congrArg (fun p => JetSer.fnVal (A := Jet V (Fin 1 × Fin d) m) p U f) e).symm.trans
      (h2.trans (by rw [ev_pt_one]; exact toJet_eq m g))
  refine ⟨h1' (show y ∈ (⊤ : (Sp (Jet V (Fin 1 × Fin d) m)).Opens) from trivial), ?_⟩
  rw [← h2']
  exact (JetSer.valSer_germ_fnVal (A := Jet V (Fin 1 × Fin d) m) (xT m).left U h1' y f).symm

def diagSub {d : ℕ} (m : ℕ) (φ : Pt V 1 d) : Jet V (Fin 2 × Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (φ j)] :
      Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) V) p.1 p.2

theorem psIn_one {d : ℕ} (m : ℕ) (f : PS V 1 d) : psIn d m ![(0 : Fin 1)] f = psTrunc m f := by
  unfold psIn
  have : (fun p : Fin 1 × Fin d => ((![(0 : Fin 1)] : Fin 1 → Fin 1) p.1, p.2)) = id := by
    funext p
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [this, MvPolynomial.rename_id_apply]

theorem diagSub_zero {d : ℕ} (m : ℕ) (φ : Pt V 1 d) : (diagSub m φ).comp (jetCopy d m 0) = AlgHom.id V _ := by
  refine Chart.jet_ext (R := V) fun p => ?_
  obtain ⟨a, i⟩ := p
  obtain rfl : a = 0 := Subsingleton.elim _ _
  show diagSub m φ (jetCopy d m 0 (Ideal.Quotient.mk _ (MvPolynomial.X _))) = Ideal.Quotient.mk _ (MvPolynomial.X _)
  rw [jetCopy, LinkLaw.jetMap_coord, diagSub, jetSubstP, LinkLaw.jetMap_coord]
  simp

theorem diagSub_one {d : ℕ} (m : ℕ) (φ : Pt V 1 d) :
    (diagSub m φ).comp (jetCopy d m 1) = jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2) := by
  refine Chart.jet_ext (R := V) fun p => ?_
  show diagSub m φ (jetCopy d m 1 (Ideal.Quotient.mk _ (MvPolynomial.X _))) =
    jetSubstP m (fun p : Fin 1 × Fin d => psTrunc m (φ p.2)) (Ideal.Quotient.mk _ (MvPolynomial.X _))
  rw [jetCopy, LinkLaw.jetMap_coord, diagSub, jetSubstP, LinkLaw.jetMap_coord, jetSubstP, LinkLaw.jetMap_coord]
  simp [psIn_one]

theorem diagSub_psJet {d : ℕ} (m : ℕ) (φ : Pt V 1 d) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (ε : PS V 2 d) :
    diagSub m φ (psJet m ε) = psJet m (ev (n := 1) ![pt V (n := 1) d 0, comp1 φ (pt V (n := 1) d 0)] ε) := by
  have c : comp1 φ (pt V (n := 1) d 0) = φ := funext fun i => ev_pt_one _
  rw [c]
  have h0 : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff
      ((![pt V (n := 1) d 0, φ] : Fin 2 → Pt V 1 d) p.1 p.2) = 0 := by
    rintro ⟨a, i⟩
    fin_cases a
    · simp [pt]
    · exact hφ i
  obtain ⟨Φ, hΦ, hsub⟩ := LinkLaw.exists_subst
    (fun p : Fin 2 × Fin d => (![pt V (n := 1) d 0, φ] : Fin 2 → Pt V 1 d) p.1 p.2) h0 m
  have e : diagSub m φ = Φ := by
    refine Chart.jet_ext (R := V) fun p => Eq.trans ?_ (hΦ p).symm
    obtain ⟨a, i⟩ := p
    fin_cases a
    · refine Eq.trans ?_ (JetSer.toJet_X m ((0 : Fin 1), i)).symm
      have := AlgHom.congr_fun (diagSub_zero m φ) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))
      rw [AlgHom.comp_apply, jetCopy, LinkLaw.jetMap_coord] at this
      exact this
    · have := AlgHom.congr_fun (diagSub_one m φ) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))
      rw [AlgHom.comp_apply, jetCopy, LinkLaw.jetMap_coord,
        LinkLaw.jetSubstP_coord m (fun p : Fin 1 × Fin d => φ p.2) _ (hφ _)] at this
      exact this
  rw [e, ← toJet_eq, ← toJet_eq]
  exact hsub ε

theorem homAt_comp' {A B C : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] [CommRing C] [Algebra V C]
    (f : A →ₐ[V] B) (g : B →ₐ[V] C) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) g ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) f = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (g.comp f) := by
  apply Over.OverMorphism.ext
  exact (Spec.map_comp _ _).symm

theorem val_prim_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (hp : Function.Surjective t.G.hom.appTop.hom) (wP : PrimTyG t) (hw : IsPrimG t wP)
    (ρ : LB.Gen (LB.LinComb t.PP.L (JetSer.primφ (t.act.act H.w0)) JetSer.primε)) (hρ : ρ.IsGen)
    (hc : LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ ρ (eSec t.G)) t.PP.rig)
    {Z : Scheme.{0}} (r : Z ⟶ t.G.left) (z : Z) (J) (hJ : Good t.PP.L z J) : val wP r z J = val ρ r z J := by
  have he : eSec t.G ≫ t.G.hom = 𝟙 S := Over.w η[t.G]
  refine gen_unique' t.PP.isLB (fun U _ k => ?_) t.G.hom (eSec t.G) he hp hw.1 hρ (fun y J hJ => ?_) Z r z J hJ
  · have P := JetSer.prod_prim (t.act.act H.w0) (𝟙 t.G) k
    simp only [Over.id_left, Category.id_comp] at P
    refine P.trans (Eq.symm ((DVR.prod_sum₂ (K := Fin 1) (U := U) _ (c := k (𝟙 _))
      (by rw [Fintype.prod_unique]; exact zpow_one _)
      (DVR.prod_neg _ _ (JetSer.prod_lam (𝟙 t.G) (t.act.act H.w0) k))).trans ?_))
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, Over.id_left]
    abel
  · have a := val_corr hJ hw.2 (𝟙 _)
    have b := val_corr hJ hc (𝟙 _)
    rw [val_pull hJ, Category.id_comp] at a b
    exact a.trans b.symm

theorem linkSec : LinkSecSt := by
  intro E _ _ _ H V _ _ t hp d BT tg xT eT wPT hC hF hW x _ hM j _ ρ hρ hc ε hε q σ r S g hr hS hg m y J hJ
  letI := H.starRing
  obtain ⟨hj, vr⟩ := gs_of_isSer1 xT x hM _ _ r hr m y
  obtain ⟨-, vS⟩ := gs_of_isSer1 xT x hM _ _ S hS m y
  let s := Formalism.L2.Pj.homAt (𝟙 (Sp V)) (diagSub m (BT.A.act H.w0))
  have h₀ : s ≫ jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2) = xT m := by
    rw [jptG, ← Category.assoc, homAt_comp', diagSub_zero]
    refine Eq.trans (congrArg (· ≫ xT m) ?_) (Category.id_comp _)
    apply Over.OverMorphism.ext
    exact Spec.map_id _
  have h₁ : s ≫ jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2) = xT m ≫ t.act.act H.w0 := by
    rw [jptG, ← Category.assoc, homAt_comp', diagSub_one]
    exact (hC.act m H.w0).symm
  obtain ⟨hs, c, c₁, c₂⟩ := change_index (t.act.act H.w0) (xT m) s _ _ h₀ h₁ (eT m) (hF.gen m) ρ hρ q σ j y hj J hJ
  obtain ⟨J₂, hJ₂, e₂⟩ := exists_good t.PP.L t.PP.isLB (s.left y)
    (cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)]) (fun _ => j)
    (fun _ _ _ => rfl) (fun I => Set.mem_iInter.1 hs I)
  have e₂' : ∀ I, J₂ (𝟙 _ ≫ cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)] I) = j :=
    fun I => (congrArg J₂ (Category.id_comp _)).trans (e₂ I)
  have v₂ := hε m (s.left y) J₂ hJ₂ e₂'
  have v₃ := (gs_unit (𝟙 _) (s.left y) _ hs _).trans
    ((congrArg Units.val (val_of (L := t.PP.L) (ε := cε 2) (eT m) (𝟙 _) (s.left y) J₂ (fun _ => j) e₂')).symm.trans v₂)
  have vε : (gm s.left y _ ((eT m).s fun _ => j)).val = germAt _ y (psJet m (diagSer BT H.w0 ε)) :=
    (gs_unit s.left y _ hs _).symm.trans ((gs_stalkMap s.left y _ hs _).trans
      ((congrArg (s.left.stalkMap y).hom v₃).trans ((gs_stalkMap s.left y ⊤ trivial _).symm.trans
        ((gs_spMap_germAt _ y _).trans (congrArg (germAt _ y) (diagSub_psJet m _ (BT.A.const H.w0) ε))))))
  have vρ : (gm (xT m).left y _ (ρ.s fun _ => j)).val = germAt _ y (psJet m r) :=
    (gs_unit (xT m).left y _ hj _).symm.trans vr
  have vL : val (eLG t (𝟙 (Sp V)) d xT BT.A.act eT wPT m) (𝟙 (Sp (Jet V (Fin 1 × Fin d) m))) y J =
      c * (gm (xT m).left y _ (ρ.s fun _ => j) * gm s.left y _ ((eT m).s fun _ => j)) := by
    refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) c₂)
    · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_prim_eq t hp wPT hW ρ hρ hc (xT m).left y J hJ))
      exact congrArg (fun p => val wPT p y J) (Category.id_comp _)
    · refine (val_pull hJ _ _ _).trans ?_
      exact congrArg (fun p => val (L := t.PP.L) (ε := cε 2) (eT m) p y J) (Category.id_comp _)
  rw [vL, gs_toΓ_eq]
  refine c₁.trans ((congrArg (_ * ·) vS).trans ?_)
  rw [← hg, FBIdJet.psJet_mul, psJet_pow, FBIdJet.psJet_mul, map_mul, map_pow, map_mul, ← vε, ← vρ]
  simp only [Units.val_pow_eq_pow_val, Units.val_mul]
  ring

end GlobalTheory.LinkSec
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.TruncationFramesLocalSeriesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.truncation_frames_local_series : LinkEpsSt := by
  first | exact @GlobalTheory.LinkEps.linkEps | exact GlobalTheory.LinkEps.linkEps | (intros; apply GlobalTheory.LinkEps.linkEps <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartFromPointDatumOfLaws

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChartLink

theorem cubical_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (h : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom) {L : RigLB G} (c c' : CubicalStr G L) : c = c' := by
  have e : c.t.s = c'.t.s := by
    refine JetSer.gen_ext_val (φ := thφ G (x3 G)) (ε := thε) L.isLB c.isGen c'.isGen fun y J hJ => ?_
    refine gen_unique L.isLB (G ⊗ G ⊗ G).hom (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left (Over.w _) h c.isGen c'.isGen
      (fun y J hJ => ?_) _ _ y J hJ
    exact ((isCub_cubV c (T := 𝟙_ (Over S)) hJ).face 1 1).trans ((isCub_cubV c' (T := 𝟙_ (Over S)) hJ).face 1 1).symm
  obtain ⟨⟨s⟩, _, _, _, _, _⟩ := c
  obtain ⟨⟨s'⟩, _, _, _, _, _⟩ := c'
  obtain rfl : s = s' := e
  rfl

theorem surjective_of_sq {S : Scheme.{0}} {G : Over S} (h : Function.Surjective (G ⊗ G).hom.appTop.hom) :
    Function.Surjective G.hom.appTop.hom := by
  intro f
  obtain ⟨a, ha⟩ := h ((fst G G).left.appTop.hom f)
  refine ⟨a, ?_⟩
  have e₁ : (lift (𝟙 G) (𝟙 G)).left ≫ (G ⊗ G).hom = G.hom := Over.w _
  have e₂ : (lift (𝟙 G) (𝟙 G)).left ≫ (fst G G).left = 𝟙 _ := congrArg (fun q => q.left) (lift_fst (𝟙 G) (𝟙 G))
  have := congrArg (lift (𝟙 G) (𝟙 G)).left.appTop.hom ha
  rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
    ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, e₁, e₂] at this
  simpa using this

theorem psJet_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {κ : Type} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (g : MvPowerSeries κ R) : psJet m (MvPowerSeries.map f g) = jetCoef f κ m (psJet m g) := by
  unfold psJet jetCoef
  rw [Ideal.Quotient.lift_mk, RingHom.comp_apply]
  congr 1
  unfold psTrunc

  simp [map_sum, MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem germA_comb {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D : DegData V I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {κ : Type} [Fintype κ] [DecidableEq κ] (z : JetPts G κ) (τ : Frames U.LG.L z) (hτ : τ.Gen)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (q : ℕ)
    {l : ℕ} (c : Fin l → F) (σ : Fin l → H0 U.LG.L q) (g : Fin l → MvPowerSeries κ V)
    (hσ : ∀ i m (y : Sp (Jet V κ m)) J, Good U.LG.L y J →
      sval (σ i) (z m).left y J = gs (𝟙 _) y ⊤ (toΓ _ (psJet m (g i))) * (val (τ m) (𝟙 _) y J ^ q).val)
    (σ' : U.SecGF F q)
    (hlin : GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => (q : ℤ)) σ'
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (q : ℤ)) σ (UnifPre.gFK (G := G) F)
      (fun i => scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (c i))) :
    GermA U z τ F q σ' (∑ i, c i • MvPowerSeries.map (algebraMap V F) (g i)) := by
  intro m
  have hL := U.LG.isLB
  have key : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet V κ m)) (y : Z) (J), Good U.LG.L y J →
      sval (σ i) (r ≫ (z m).left) y J = cst r y (psJet m (g i)) * (val (τ m) r y J ^ q).val := by
    intro i
    obtain ⟨v, hv⟩ := ExpansionValueZero.exists_coeff (A := Jet V κ m) hL (σ i) (z m).left
      (GeneratorPullback.powGen U.LG.L _ _ (τ m) q) (powGen_isGen_of_isGen _ (hτ m) q)
      (fun W _ h => by simp only [Category.comp_id, _root_.mul_one])
    have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet V κ m)) (y : Z) (J), Good U.LG.L y J →
        sval (σ i) (r ≫ (z m).left) y J = cst r y v * (val (τ m) r y J ^ q).val := fun Z r y J hJ =>
      (hv Z r y J hJ).trans (congrArg (fun u => cst r y v * Units.val u) (map_pow _ _ _))
    obtain rfl : v = psJet m (g i) := H1.cst_ext fun y => by
      obtain ⟨J, hJ, -⟩ := exists_good U.LG.L hL y (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => k.elim) (fun k => k.elim)
      have e := hv' _ (𝟙 _) y J hJ
      rw [Category.id_comp] at e
      exact (Units.mul_left_inj _).1 (e.symm.trans (hσ i m y J hJ))
    exact hv'
  obtain ⟨a, a₁, a₂⟩ := GermBasic.exists_jetPt (F := F) z m
  refine ⟨a, a₁, a₂, fun y J hJ => ?_⟩
  refine (BoxExpansion.secLin_val hlin a y hJ).trans ?_
  have e : gs (𝟙 _) y ⊤ (toΓ _ (psJet m (∑ i, c i • MvPowerSeries.map (algebraMap V F) (g i)))) =
      ∑ i, cst (𝟙 _) y (algebraMap F (Jet F κ m) (c i)) *
        cst (𝟙 _) y (psJet m (MvPowerSeries.map (algebraMap V F) (g i))) := by
    refine (congrArg (cst (𝟙 _) y) (GermBasic.psJet_sum m c _)).trans ((ExpansionValueZero.cst_sum _ _ _ _).trans ?_)
    exact Finset.sum_congr rfl fun i _ => H1.cst_mul _ _ _ _
  rw [e, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [a₂, key i _ _ y J hJ, _root_.mul_assoc]
  refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) ?_ rfl)
  · refine (gs_pull a _ y ⊤ trivial _).trans ?_
    rw [a₁, ← ExpansionValueZero.cst_comp, Category.id_comp]
    rfl
  · rw [psJet_map, ← ExpansionValueZero.cst_comp, Category.id_comp]

theorem exists_chartData {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {V : Type} [CommRing V]
    [IsLocalRing V] (t : SAB H (Sp V)) (Lr : RigLB t.G) (h : Lr = t.PP) (c : CubicalStr t.G Lr)
    (s₂ : Function.Surjective (t.G ⊗ t.G).hom.appTop.hom)
    (s₃ : Function.Surjective (t.G ⊗ t.G ⊗ t.G).hom.appTop.hom) :
    letI := H.starRing
    ∀ (d : ℕ) (BT : FB V d (𝓞 E)) (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
      (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t),
      IsChartG t (𝟙 (Sp V)) d BT.G.F BT.A.act tg (fun j : Fin d => Pi.single j (1 : V)) xT →
      IsFrameG t (𝟙 (Sp V)) d xT BT.G.F BT.A.act BT.ph1 BT.ph2 BT.sy BT.ad eT → IsPrimG t wPT →
      IsUnivJ t.G (Fin 1 × Fin d) xT → FrTrunc t (𝟙 (Sp V)) d xT eT →
    ∀ τ : Frames Lr.L (κ := Fin 1 × Fin d) xT,
      (∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → Lr.L.ι),
        Good Lr.L y J → val (τ m) (𝟙 _) y J =
          val (genCast (congrArg RigLB.L h).symm _ _ (eLG t (𝟙 (Sp V)) d xT BT.A.act eT wPT m)) (𝟙 _) y J) →
    ∃ (x : JetSer.Fam t.G (Fin d)) (j : Lr.L.ι)
      (u : ∀ a : 𝓞 E, LB.Gen (LB.LinComb Lr.L (rosatiφ t.G (t.act.act a) (t.act.act (star a))) rosatiε))
      (B : FB V d (𝓞 E)) (ρ : LB.Gen (LB.LinComb Lr.L (JetSer.primφ (t.act.act H.w0)) JetSer.primε)) (ε : PS V 2 d),
      Chart.IsUnivChart t.G d x ∧ ⊤ ≤ η[t.G].left ⁻¹ᵁ Lr.L.U j ∧ (∀ a, JetSer.IsNormRos Lr.L _ _ (u a)) ∧
      JetSer.IsFBOf Lr c t.act u x j B ∧ ρ.IsGen ∧ JetSer.Related B BT (pt V (n := 1) d 0) (pt V (n := 1) d 0) ε ∧
      ∀ (q : ℕ) (σ : H0 Lr.L q) (r S g : PS V 1 d), JetSer.IsSer1 x _ (ρ.s (fun _ => j)).val r →
        JetSer.IsSer1 x _ (σ.f (fun _ => j)) S → g * (diagSer BT H.w0 ε * r) ^ q = S →
        ∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → Lr.L.ι),
          Good Lr.L y J →
          sval σ (xT m).left y J = gs (𝟙 _) y ⊤ (toΓ _ (psJet m g)) * (val (τ m) (𝟙 _) y J ^ q).val := by
  subst h
  obtain rfl : c = t.cub := cubical_eq s₃ _ _
  letI := H.starRing
  intro d BT tg xT eT wPT hC hF hW hU hT τ hEL
  obtain ⟨x, hx, hM⟩ := univConv V t.G _ xT hU d (oneCol d)
  obtain ⟨j, hj⟩ := JetSer.exists_index_of_local t.PP.L t.PP.isLB η[t.G].left
  have hu : ∀ a : 𝓞 E, ∃ u, JetSer.IsNormRos t.PP.L (t.act.act a) (t.act.act (star a)) u := fun a => by
    have := t.act.hom a
    have := t.act.hom (star a)
    exact (NormRos.normRos_of_lbIso _ t.G t.PP.L t.PP.isLB _ _ (t.adj a)).1
  choose u hu using hu
  obtain ⟨B, hB⟩ := JetRoad.jetRoad.2.2.2.2.2.2.2.2.2.1 V t.G s₂ s₃ t.PP t.cub (𝓞 E) t.act u hu d x hx j hj
  have := t.act.hom H.w0
  obtain ⟨ρ, hρ, hρc⟩ := (JetSer.exists_unique_normPrim _ t.G t.PP (t.act.act H.w0) t.prim).1
  obtain ⟨ε, hε⟩ := GlobalTheory.T.truncation_frames_local_series E H V t d _ _ _ _ _ _ tg xT eT wPT hC hF hW hT j hj
  refine ⟨x, j, u, B, ρ, ε, hx, hj, hu, hB, hρ,
    LinkRel.linkRel E H V t s₂ d BT tg xT eT wPT hC hF hW x hx hM j hj u hu B hB ε hε,
    fun q σ r S g hr hS hg m y J hJ => ?_⟩
  rw [hEL m y J hJ]
  exact LinkSec.linkSec E H V t (surjective_of_sq s₂) d BT tg xT eT wPT hC hF hW x hx hM j hj ρ hρ hρc ε hε q σ r S g
    hr hS hg m y J hJ

theorem isUnit_diagSer {V : Type} [CommRing V] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {B B' : FB V d O}
    {φ φi : Pt V 1 d} {ε : PS V 2 d} (h : JetSer.Related B B' φ φi ε) (w0 : O) : IsUnit (diagSer B' w0 ε) := by
  have e₀ : MvPowerSeries.constantCoeff ε = 1 := by
    rw [← GaugeAdjoint.constantCoeff_ev (a := ![0, pt V (n := 1) d 0]) (fun j i => by fin_cases j <;> simp [pt]) ε,
      h.ax0, map_one]
  have c : comp1 (B'.A.act w0) (pt V (n := 1) d 0) = B'.A.act w0 := funext fun i => LinkSec.ev_pt_one _
  rw [MvPowerSeries.isUnit_iff_constantCoeff, diagSer, c, GaugeAdjoint.constantCoeff_ev (fun j i => ?_) ε, e₀]
  · exact isUnit_one
  · fin_cases j
    · simp [pt]
    · exact B'.A.const w0 i

theorem linkSt_holds : LinkSt := by
  intro E _ _ _ H V _ _ _ hc t P tors ϖ hϖ Q hQ F _ _ _ _ v hv d BT tg xT eT wPT hC hF hW hU hT τ hτ hEL
  letI := H.starRing
  obtain ⟨s₂, s₃⟩ := FamGerm.surjective_appTop_sq_cube P.U.toUnifPre
  obtain ⟨x, j, u, B, ρ, ε, hx, hj, hu, hB, hρ, hR, hS⟩ := exists_chartData H t P.U.LG P.bundle P.U.cubG s₂ s₃
    d BT tg xT eT wPT hC hF hW hU hT τ hEL
  refine ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, ε, hR, ?_⟩
  rintro q s f f' ⟨l, c, σ, fi, g, r, h₁, h₂, h₃, h₄, h₅⟩ hf
  obtain ⟨w, hw⟩ := (isUnit_diagSer hR H.w0).exists_right_inv
  obtain ⟨σ', hσ'⟩ := BoxExpansion.exists_secLin P.U.LG.isLB
    (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj t.G)).left (UnifPre.gFK (R := V) (G := t.G) F)
    (fun _ : Fin 1 => UnifPre.gFK (R := V) (G := t.G) F) (fun _ => (Category.comp_id _).symm) σ c
  refine ⟨σ', ⟨l, c, σ, fi, h₁, hσ', h₂⟩, ?_⟩
  have eV : TWO.algVF (V := V) (F := F) = algebraMap V F := (IsScalarTower.algebraMap_eq V _ F).symm
  have e : f' = ∑ i, c i • MvPowerSeries.map (algebraMap V F) (g i * w ^ q) := by
    have e₁ : f' = f * MvPowerSeries.map (algebraMap V F) (w ^ q) := by
      rw [← hf, _root_.mul_assoc, ← map_pow, ← map_mul, ← mul_pow, hw, one_pow, map_one, _root_.mul_one]
    rw [e₁, h₅, Finset.sum_mul, eV]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPowerSeries.smul_eq_C_mul, _root_.mul_assoc]
  rw [e]
  refine germA_comb P.U.toUnifPre xT τ hτ F q c σ _ (fun i m y J hJ => ?_) σ' hσ'
  obtain ⟨S, hS₁, hS₂⟩ := h₄ i
  refine hS q (σ i) r S _ h₃ hS₁ ?_ m y J hJ
  rw [← hS₂, _root_.mul_assoc, ← mul_pow, ← _root_.mul_assoc, _root_.mul_comm w, hw, _root_.one_mul]

theorem link : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → LinkSt := fun _ _ _ _ => linkSt_holds

end GlobalTheory.ChartLink
end
end
end
