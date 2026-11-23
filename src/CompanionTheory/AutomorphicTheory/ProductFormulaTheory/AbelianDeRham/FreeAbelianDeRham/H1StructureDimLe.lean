module

public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechTripleRestrictCompositeInjectiveCohomologyFo
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeExOfAcyclic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1BoundaryOfBoundary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExactOfSpan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteCover
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsToCoindShortExact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyOfBaseZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HtpyStOfCxSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Pull1RestrictPairRestriction
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SteinOfBijective
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimSmoothSurjectiveTotal
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.AbelianSchemeSpreadsOverLocalization
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularCurve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.TypeStar
import Mathlib.AlgebraicGeometry.QuasiAffine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechNerveFaceOneZero

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QIsoAtRight

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.QCalc

section Linear

variable {R A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ C₂ : Type} [CommRing R]
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
  [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂]
  [Module R A₀] [Module R A₁] [Module R A₂]
  [Module R B₀] [Module R B₁] [Module R B₂]
  [Module R C₀] [Module R C₁] [Module R C₂]
  {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂}
  {c₀ : C₀ →ₗ[R] C₁} {c₁ : C₁ →ₗ[R] C₂}
  {f₀ : A₀ →ₗ[R] B₀} {f₁ : A₁ →ₗ[R] B₁} {f₂ : A₂ →ₗ[R] B₂}
  {g₀ : B₀ →ₗ[R] C₀} {g₁ : B₁ →ₗ[R] C₁} {g₂ : B₂ →ₗ[R] C₂} {k : A₁ →ₗ[R] C₁}

theorem qIsoAt_comp (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x)) (hg₀ : ∀ x, g₁ (b₀ x) = c₀ (g₀ x))
    (hk : ∀ x, k x = g₁ (f₁ x)) (hf : QIsoAt a₀ a₁ b₀ b₁ f₁) (hg : QIsoAt b₀ b₁ c₀ c₁ g₁) :
    QIsoAt a₀ a₁ c₀ c₁ k := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · have hc : b₁ (f₁ x) = 0 := by rw [← hf₂, hx, map_zero]
    exact hf.1 x hx (hg.1 (f₁ x) hc ⟨y, by rw [hy, hk]⟩)
  · obtain ⟨w, y, hw, hy⟩ := hg.2 z hz
    obtain ⟨x, y', hx, hy'⟩ := hf.2 w hw
    refine ⟨x, y + g₀ y', hx, ?_⟩
    have e : f₁ x = w + b₀ y' := by rw [← hy']; abel
    rw [hk, e, map_add (f := _), hg₀, map_add (f := _), ← hy]
    abel

theorem qIsoAt_right (hf₀ : ∀ x, f₁ (a₀ x) = b₀ (f₀ x)) (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x))
    (hg₀ : ∀ x, g₁ (b₀ x) = c₀ (g₀ x)) (hk : ∀ x, k x = g₁ (f₁ x))
    (hf : QIsoAt a₀ a₁ b₀ b₁ f₁) (hK : QIsoAt a₀ a₁ c₀ c₁ k) :
    QIsoAt b₀ b₁ c₀ c₁ g₁ := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨u, v, hu, hv⟩ := hf.2 x hx
    have e : f₁ u = x + b₀ v := by rw [← hv]; abel
    obtain ⟨w, hw⟩ := hK.1 u hu ⟨y + g₀ v, by rw [hk, e, map_add (f := _), map_add (f := _), hg₀, hy]⟩
    refine ⟨f₀ w - v, ?_⟩
    rw [map_sub, ← hf₀, hw, e]
    abel
  · obtain ⟨x, y, hx, hy⟩ := hK.2 z hz
    refine ⟨f₁ x, y, by rw [← hf₂, hx, map_zero], ?_⟩
    rw [← hk]
    exact hy

theorem qIsoAt_left (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x))
    (hg₀ : ∀ x, g₁ (b₀ x) = c₀ (g₀ x)) (hg₂ : ∀ x, g₂ (b₁ x) = c₁ (g₁ x))
    (hk : ∀ x, k x = g₁ (f₁ x))
    (hg : QIsoAt b₀ b₁ c₀ c₁ g₁) (hK : QIsoAt a₀ a₁ c₀ c₁ k) :
    QIsoAt a₀ a₁ b₀ b₁ f₁ := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · exact hK.1 x hx ⟨g₀ y, by rw [← hg₀, hy, hk]⟩
  · have hc : c₁ (g₁ z) = 0 := by rw [← hg₂, hz, map_zero]
    obtain ⟨x, y, hx, hy⟩ := hK.2 (g₁ z) hc
    have hd : b₁ (f₁ x - z) = 0 := by rw [map_sub, ← hf₂, hx, hz, map_zero, sub_zero]
    obtain ⟨y', hy'⟩ := hg.1 (f₁ x - z) hd ⟨y, by rw [map_sub, ← hk, hy]⟩
    exact ⟨x, y', hx, hy'.symm⟩

end Linear

theorem qCalcSt : CxSt → QCalcSt := by
  intro hCx R _ C _ F D E _ _ G H m n k hk
  have cm : ∀ i x, pulln m (i + 1) (dn F i x) = dn G i (pulln m i x) :=
    fun i x ↦ LinearMap.congr_fun ((hCx R C F).2 D G m i) x
  have cn : ∀ i x, pulln n (i + 1) (dn G i x) = dn H i (pulln n i x) :=
    fun i x ↦ LinearMap.congr_fun ((hCx R D G).2 E H n i) x
  have zf : ∀ x : R, pulln m 0 ((0 : R →ₗ[R] Cn F 0) x) =
      (0 : R →ₗ[R] Cn G 0) ((0 : R →ₗ[R] R) x) := fun x ↦ by simp
  have zg : ∀ x : R, pulln n 0 ((0 : R →ₗ[R] Cn G 0) x) =
      (0 : R →ₗ[R] Cn H 0) ((0 : R →ₗ[R] R) x) := fun x ↦ by simp
  refine ⟨fun h₁ h₂ ↦ ⟨?_, fun i ↦ ?_⟩, fun h₁ h₂ ↦ ⟨?_, fun i ↦ ?_⟩, fun h₁ h₂ ↦ ⟨?_, fun i ↦ ?_⟩⟩
  · exact qIsoAt_comp (cm 0) zg (hk 0) h₁.1 h₂.1
  · exact qIsoAt_comp (cm (i + 1)) (cn i) (hk (i + 1)) (h₁.2 i) (h₂.2 i)
  · exact qIsoAt_right zf (cm 0) zg (hk 0) h₁.1 h₂.1
  · exact qIsoAt_right (cm i) (cm (i + 1)) (cn i) (hk (i + 1)) (h₁.2 i) (h₂.2 i)
  · exact qIsoAt_left (cm 0) zg (cn 0) (hk 0) h₁.1 h₂.1
  · exact qIsoAt_left (cm (i + 1)) (cn i) (cn (i + 1)) (hk (i + 1)) (h₁.2 i) (h₂.2 i)

end GlobalTheory.CompanionTheory.QCalc
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopologicalKrullDimLeOfSmooth

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge

theorem topologicalKrullDim_le_of_smooth {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Sp k) (g : ℕ)
    (hf : SmoothOfRelativeDimension g f) : topologicalKrullDim X ≤ g := by
  rw [GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_iSup_stalk]
  exact iSup_le fun x ↦ GroundTheory.Arith.SchemeCoh.ringKrullDim_stalk_le_of_smoothOfRelativeDimension g f x

theorem subsingleton_coh_abelian (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (g n : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (hn : g < n) :
    Subsingleton (GlobalTheory.coh (GlobalTheory.structureModule A.left) n) := by
  refine GlobalTheory.subsingleton_coh_of_isProjOver (PositivityTheory.Xgn.AbelianSchemeSpreading.isProjOver_abelian k A hA) _ ?_
  refine lt_of_le_of_lt ((topologicalKrullDim_subspace_le _ _).trans
    (topologicalKrullDim_le_of_smooth A.hom g hg)) ?_
  exact_mod_cast hn

theorem exact_of_subsingleton_Hs {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (n : ℕ) (hdd : dn F (n + 1) ∘ₗ dn F n = 0) (h : Subsingleton (Hs F n)) :
    Function.Exact (dn F n) (dn F (n + 1)) := by
  intro x
  constructor
  · intro hx
    have hm : (⟨x, hx⟩ : LinearMap.ker (dn F (n + 1))) ∈
        (LinearMap.range (dn F n)).comap (LinearMap.ker (dn F (n + 1))).subtype :=
      (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)
    exact hm
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun hdd y

theorem vanSt (hCx : CxSt) (hCmp : CmpSt) : VanSt := by
  intro R _ A _ g hA hg hR P _ _ S n hn
  letI := hR.toField
  have hsep : IsSeparated A.hom := by
    have := hA.proper
    infer_instance
  obtain ⟨e⟩ := (hCmp R A.left A.hom hsep P S).2 n
  have hs : Subsingleton (GlobalTheory.coh (GlobalTheory.structureModule A.left) (n + 1)) :=
    subsingleton_coh_abelian R A g (n + 1) hA hg (Nat.lt_succ_of_le hn)
  exact exact_of_subsingleton_Hs _ n ((hCx R _ (OSys A.hom S)).1 n) e.toEquiv.subsingleton

end GlobalTheory.CompanionTheory.Hodge
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeOfBijective

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.WedgeField

theorem exists_finite_sys {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsSeparated s]
    [CompactSpace X] :
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  have hinter : ∀ U W : X.Opens, IsAffineOpen U → IsAffineOpen W → IsAffineOpen (U ⊓ W) :=
    fun U W hU hW => isAffineHom_diagonal_iff.mp
      (inferInstance : IsAffineHom (Limits.pullback.diagonal s)) ⊤ (isAffineOpen_top _) U le_top W le_top hU hW
  have hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, (U.1 : Set X) := fun x _ => by
    have hx : x ∈ (⨆ U : X.affineOpens, U.1 : X.Opens) := by
      rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact Set.mem_iUnion.2 ⟨U, hU⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) hcov
  let A : Set X.Opens := (fun U : X.affineOpens => U.1) '' (t : Set X.affineOpens)
  have hfin : (infClosure A).Finite := (t.finite_toSet.image _).infClosure
  have haff : infClosure A ⊆ {V : X.Opens | IsAffineOpen V} :=
    infClosure_min (by rintro _ ⟨U, _, rfl⟩; exact U.2) fun a ha b hb => hinter a b ha hb
  letI inst : SemilatticeInf (infClosure A) :=
    Subtype.semilatticeInf fun x y hx hy => infClosed_infClosure hx hy
  refine ⟨infClosure A, inst, hfin.to_subtype, ⟨⟨fun p => ⟨p.1, haff p.2⟩, fun a b => rfl, ?_⟩⟩⟩
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2
    ⟨⟨U.1, subset_infClosure ⟨U, hU, rfl⟩⟩, hx⟩

def sqEquiv {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (E : M ≃ₗ[R] N) : ⋀[R]^2 M ≃ₗ[R] ⋀[R]^2 N :=
  LinearEquiv.ofLinear (exteriorPower.map 2 (E : M →ₗ[R] N)) (exteriorPower.map 2 (E.symm : N →ₗ[R] M))
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])

theorem sqEquiv_ιMulti {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N) (a b : M) :
    sqEquiv E (exteriorPower.ιMulti R 2 ![a, b]) = exteriorPower.ιMulti R 2 ![E a, E b] := by
  change exteriorPower.map 2 (E : M →ₗ[R] N) _ = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem wedge_of_bijective {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) (h2 : Function.Bijective m.pull2) (h : Wedge F') : Wedge F := by
  obtain ⟨e, he⟩ := h
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  let E2 : H2 F ≃ₗ[R] H2 F' := LinearEquiv.ofBijective m.pull2 h2
  refine ⟨(sqEquiv E1).trans (e.trans E2.symm), fun a b => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, sqEquiv_ιMulti, he, LinearEquiv.symm_apply_eq]
  exact (m.pullCohomologyTwo_cup a b).symm

theorem vb_of_bijective {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) {n : ℕ} (h : VB R (H1 F) n) : VB R (H1 F') n := by
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  obtain ⟨hf, hp, hr⟩ := h
  refine ⟨Module.Finite.equiv E1, Module.Projective.of_equiv E1, fun p => ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv E1]
  exact hr p

end GlobalTheory.CompanionTheory.Hodge.WedgeField
end
end
end

-- Source module: CompanionTheory.AutomorphicTheory.ProductFormulaTheory.AbelianDeRham.FreeAbelianDeRham.H1StructureDimLe

section

@[expose] public section

namespace MainStatements.Hodge.Free

theorem h1Le : CompanionTheory.ObstructionTrivialLocus.H1StructureDimLe := by
  have hCx := GlobalTheory.CompanionTheory.HodgeCx.cxSt
  have hDict := GlobalTheory.CompanionTheory.Dict.dictSt
  have hLow := GlobalTheory.CompanionTheory.HodgeLow.lowSt_of_dictSt hDict
  have hHtpy := GlobalTheory.CompanionTheory.Hodge.htpySt_of_cxSt hCx
  have hQ := GlobalTheory.CompanionTheory.QCalc.qCalcSt hCx
  have hFub := GlobalTheory.CompanionTheory.NerveCoh.fubiniSt hCx
  have hAff := GlobalTheory.CompanionTheory.AffAcyc.main hCx hHtpy
  have hDesc := GlobalTheory.CompanionTheory.Descent.descentSt hCx hHtpy hQ hFub hAff
  have hBC := GlobalTheory.CompanionTheory.SysBC.sysBCSt hDesc hLow
  have hStein := GlobalTheory.CompanionTheory.Hodge.stein_holds
  have hAx := GlobalTheory.CompanionTheory.Axis.axOSt hDesc hLow hBC hStein
  have hVan := GlobalTheory.CompanionTheory.Hodge.vanSt hCx (GlobalTheory.CompanionTheory.Hodge.Nerve.cmpSt_of_cxSt hCx)
  have hHopf := GlobalTheory.CompanionTheory.HopfSys.hopfSt hHtpy hQ hFub hAff hDesc hLow hAx
  have hHopfLe := GlobalTheory.CompanionTheory.HopfLe.hopfLeSt hCx hDict hLow
  classical
  intro k _ A _ g hA hsm
  haveI : AlgebraicGeometry.IsProper A.hom := ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme.proper (self := hA)
  haveI : CompactSpace A.left := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨P, _, _, ⟨S⟩⟩ := GlobalTheory.CompanionTheory.Hodge.WedgeField.exists_finite_sys A.hom
  have hfield : IsField k := Field.toIsField k
  have hq : MainStatements.Hodge.AllQIso (MainStatements.Hodge.resSys A.hom S) := hDesc k A.left A.hom inferInstance P S
  obtain ⟨hb1, -, hst⟩ := hLow k _ _ _ _ (MainStatements.Hodge.resSys A.hom S) hq
  have hstein : MainStatements.Hodge.Stein (MainStatements.Hodge.OSys A.hom S) := hst.mp (hStein k A g hA hsm)
  have hexact := hVan k A g hA hsm hfield P S
  have hhopf : MainStatements.Hodge.Hopf (MainStatements.Hodge.OSys A.hom S) True := by
    have h := hHopf k A g hA hsm P S
    rwa [eq_true hfield] at h
  have hno := hHopfLe k P (MainStatements.Hodge.OSys A.hom S) g hfield hstein hexact hhopf
  have hn : ∀ x : Fin (g + 1) → GlobalTheory.CechDR.HO1 A.hom, ¬ LinearIndependent k x := by
    intro x hx
    exact hno (⇑(MainStatements.Hodge.resSys A.hom S).pull1 ∘ x)
      (hx.map' (MainStatements.Hodge.resSys A.hom S).pull1 (LinearMap.ker_eq_bot.mpr hb1.1))
  let b := Module.Basis.ofVectorSpace k (GlobalTheory.CechDR.HO1 A.hom)
  have hemb : ∀ e : Fin (g + 1) ↪ Module.Basis.ofVectorSpaceIndex k (GlobalTheory.CechDR.HO1 A.hom), False :=
    fun e => hn _ (b.linearIndependent.comp e e.injective)
  haveI : Finite (Module.Basis.ofVectorSpaceIndex k (GlobalTheory.CechDR.HO1 A.hom)) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    exact hemb (Fin.valEmbedding.trans (Infinite.natEmbedding _))
  haveI hfin : Module.Finite k (GlobalTheory.CechDR.HO1 A.hom) := Module.Finite.of_basis b
  refine ⟨hfin, ?_⟩
  rw [Module.finrank_eq_nat_card_basis b]
  by_contra hlt
  rw [not_le] at hlt
  exact hemb ((Fin.castLEEmb (Nat.succ_le_of_lt hlt)).trans (Finite.equivFin _).symm.toEmbedding)

end MainStatements.Hodge.Free
end
end
