module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemMoveLevUloc
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CoeffProdRename
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLatDlOfIsOrthCo
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOrthCoToLEOfCTMulSelf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSDLatLatK
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
public import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLatAndDlEqOfIsSDLatMvL

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OrthSelfDual

theorem toLE_mem_mvL {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (co : GL (Fin N) E)
    (M : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    toLE co y ∈ mvL co M ↔ y ∈ M := by
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hxy' : x = y := (toLE co).injective hxy
    rw [hxy'] at hx
    exact hx
  · intro hy
    exact Submodule.mem_map.mpr ⟨y, hy, rfl⟩

theorem isLat_and_dl_eq_of_isSDLat_mvL : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)), IsOrthCo (sp.cm.sig : E →+* E) J (toLE co) → IsSDLat E N (mvL co M) → Formalism.L2.GlobalTheoryTheory.Comp.IsLat M ∧ Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J M = M := by
  intro R F E _ _ _ _ _ _ sp N J co M hco hsd
  obtain ⟨hfg, hspan, hdual⟩ := hsd

  have hkey : ∀ x z : Fin N → E, Formalism.BasicNotions.stdH E N (toLE co x) (toLE co z) =
      ∑ a, ∑ b, (sp.cm.sig : E →+* E) (x a) * J a b * z b := fun x z => hco x z
  have hinj : Function.Injective
      (((toLE co : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E)) :=
    (toLE co).injective
  refine ⟨⟨?_, ?_⟩, ?_⟩
  ·
    have hfin : Module.Finite (𝓞 E)
        (M.map ((((toLE co : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E))).restrictScalars (𝓞 E))) :=
      Module.Finite.iff_fg.mpr hfg
    exact Module.Finite.equiv (Submodule.equivMapOfInjective _ hinj M).symm
  ·
    have himage : (↑(mvL co M) : Set (Fin N → E)) = (toLE co) '' (↑M : Set (Fin N → E)) := by
      ext x
      simp [mvL]
    rw [himage] at hspan
    apply top_unique
    intro x hx
    apply (Submodule.apply_mem_span_image_iff_mem_span
      (R := E) (R₂ := E)
      (f := ((toLE co : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)))
      (toLE co).injective).mp
    change toLE co x ∈ Submodule.span E ((toLE co) '' (↑M : Set (Fin N → E)))
    rw [hspan]
    trivial
  ·
    ext y
    rw [Formalism.L2.GlobalTheoryTheory.Comp.mem_dl, ← toLE_mem_mvL co M y, hdual (toLE co y)]
    constructor
    · intro h x' hx'
      obtain ⟨x, hx, hxx'⟩ := Submodule.mem_map.mp hx'
      have hx'' : x' = toLE co x := hxx'.symm
      rw [hx'', hkey]
      exact h x hx
    · intro h x hx
      have h1 := h (toLE co x) ((toLE_mem_mvL co M x).mpr hx)
      rw [hkey] at h1
      exact h1

end GlobalTheory.OrthSelfDual

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSDLatLatKOfStdL

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.KerSelfDual

theorem isSDLat_latK_of_stdL : ∀ {D : D7} {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) (co : GL (Fin (D.R.N i)) D.host.E) (a : 𝓞 D.host.E), cT (sigD D : D.host.E →+* D.host.E) co.1 * co.1 = gramN D i hi → latCo D.sp (gramN D i hi) co a 1 lev.Lb = StandardLatticesGL3.stdL D (D.R.N i) → ∀ x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), IsSDLat D.host.E (D.R.N i) (latK D.sp (gramN D i hi) a x.1 lev.Lb) := by
  intro D i hi T bad lev co a hco hstd x
  have hc : IsOrthCo ((sigD D : D.host.E →ₐ[D.host.F] D.host.E) : D.host.E →+* D.host.E) (gramN D i hi) (toLE co) :=
    GlobalTheory.TwV.isOrthCo_toLE_of_cT_mul_self _ _ co hco
  have hc' : ∃ c, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) c := ⟨toLE co, hc⟩
  have hJ := GlobalTheory.isLat_dl_of_isOrthCo D.sp (gramN D i hi) hc'
  have hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat lev.Lb := ⟨lev.Lb_fin, lev.Lb_span⟩
  have h1 : Formalism.L2.PairingIndexBounds.F.latAd (1 : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) lev.Lb = lev.Lb := by
    rw [GlobalTheory.SDCompan.latAd_eq]
    exact Formalism.L2.GlobalTheoryTheory.Comp.glob_one hLb
  have hm : mvL co (compan (sp := D.sp) (gramN D i hi) a lev.Lb) = StandardLatticesGL3.stdL D (D.R.N i) := by
    rw [← hstd, latCo, h1]
  have hsd := GlobalTheory.FourthRootStd.stdL_isSD D (D.R.N i)
  rw [← hm] at hsd
  obtain ⟨hM, hdl⟩ := GlobalTheory.OrthSelfDual.isLat_and_dl_eq_of_isSDLat_mvL D.sp (gramN D i hi) co _ hc hsd
  exact GlobalTheory.SDCompan.isSDLat_latK D.sp (gramN D i hi) hJ hc' x.1 x.2 lev.Lb a hLb hM hdl

end GlobalTheory.KerSelfDual
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeSelfDualEvenRankAtSite

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerSiteSelfDual

theorem isSDLat_of_heq {E : Type} [Field E] [NumberField E] [StarRing E] {n N : ℕ} (h : n = N)
    {L : Submodule (𝓞 E) (Fin n → E)} {M : Submodule (𝓞 E) (Fin N → E)} (hL : HEq L M) (hM : Formalism.BasicNotions.IsSDLat E N M) :
    Formalism.BasicNotions.IsSDLat E n L := by
  subst h
  cases hL
  exact hM



theorem even_and_isSDLat_kerN : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ j, j ≤ D.R.m → ∀ La : (sysS H X std).Lt j, ((sysS H X std).Pj j).IsLatTup La.2 → Even (((sysS H X std).Pj j).m + 1) ∧ IsSDLat D.host.E (((sysS H X std).Pj j).m + 1) ((J.fd std).kerN j La) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J hD j hj La hLa
  obtain ⟨⟨hr, -⟩, -, hk, -⟩ := hD j hj La hLa
  refine ⟨hr ▸ Formalism.MainNotions.product_zeroth_first_parts.N_even D.R j, isSDLat_of_heq hr hk ?_⟩
  exact GlobalTheory.KerSelfDual.isSDLat_latK_of_stdL ((J.St j hj).K (J.chart std j hj La)).lev (J.A.crd j hj) J.a
    (J.pins.crd_orth j hj) (J.base j hj _) (J.pt std j hj La)

end GlobalTheory.KerSiteSelfDual
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeSelfDualEvenRankAtSiteStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelLattice_selfDual_even_rank_at_site : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ j, j ≤ D.R.m → ∀ La : (sysS H X std).Lt j, ((sysS H X std).Pj j).IsLatTup La.2 → Even (((sysS H X std).Pj j).m + 1) ∧ IsSDLat D.host.E (((sysS H X std).Pj j).m + 1) ((J.fd std).kerN j La) := by
  first | exact @GlobalTheory.KerSiteSelfDual.even_and_isSDLat_kerN | exact GlobalTheory.KerSiteSelfDual.even_and_isSDLat_kerN | (intros; apply GlobalTheory.KerSiteSelfDual.even_and_isSDLat_kerN <;> assumption)
end
end
