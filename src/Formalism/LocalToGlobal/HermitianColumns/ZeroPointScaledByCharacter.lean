module

public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.HermitianColumns.CocycleZeroMemInvariants
public import Formalism.LocalToGlobal.HermitianColumns.CoordinateLatticeSelfDual

-- Source module: Formalism.LocalToGlobal.HermitianColumns.SplitGAlg

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

structure ColLevelX {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} (L : ColLevel R F E sp gp C A clsLat)
    (inK : E → Prop) (piU : 𝓞 E)
    (e : A.vT ≃ {v : HeightOneSpectrum (𝓞 F) // ((A.T : ℕ) : 𝓞 F) ∈ v.asIdeal})
    (fz : ∀ (v : A.vT) (c : C.cls 0), Formalism.HermitianLatticesTheory.dual (sp.X 0).hT (clsLat 0 c) → A.Fv v) where

  piG : Fin 2 → 𝓞 E
  piG_K : ∀ i, inK (piG i : E)
  piG_norm : ∀ i, (piG i : E) * star (piG i : E) = (gp i : E)

  splitG_pi : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal),
    Valued.v (L.splitG i v h (inclE (F := F) (v.adicCompletion F) (star (piG i : E)))).1 < 1

  splitG_alg : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (a : v.adicCompletion F),
    L.splitG i v h ((1 : E) ⊗ₜ[F] a) = (a, a)

  frG_lat : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal)
    (t : Fin R.k → v.adicCompletion F),
    (∃ x ∈ locL v L.Lb, ∀ a, (L.splitG i v h (x a)).1 = t a) ↔
      ∀ a, (((L.frG i v h)⁻¹ : GL (Fin R.k) (v.adicCompletion F)) :
        Matrix (Fin R.k) (Fin R.k) (v.adicCompletion F)).mulVec t a ∈ v.adicCompletionIntegers F

  fM_pi : ∀ (v : HeightOneSpectrum (𝓞 F)) (h : ((A.T : ℕ) : 𝓞 F) ∈ v.asIdeal) (a : intV E v),
    (a : E ⊗[F] v.adicCompletion F) = inclE (F := F) (v.adicCompletion F) (piU : E) →
    ∀ m : L.fM v h, a • m = 0

  fMe : ∀ (w : HeightOneSpectrum (𝓞 F)) (h : ((A.T : ℕ) : 𝓞 F) ∈ w.asIdeal), L.fM w h ≃+ A.Fv (e.symm ⟨w, h⟩)

  fv0 : ∀ (w : HeightOneSpectrum (𝓞 F)) (h : ((A.T : ℕ) : 𝓞 F) ∈ w.asIdeal) (c : C.cls 0)
    (z : Formalism.HermitianLatticesTheory.dual (sp.X 0).hT (clsLat 0 c))
    (t : latS (F := F) (w.adicCompletion F) (intV E w)
      (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb))),
    ((bc (prV (E := E) w) (L.y c : GL (Fin R.k) (E ⊗[F] Af F)) : GL (Fin R.k) (E ⊗[F] w.adicCompletion F)) :
      Matrix (Fin R.k) (Fin R.k) (E ⊗[F] w.adicCompletion F)).mulVec t.1 =
      (fun a => inclE (F := F) (w.adicCompletion F) (sp.crd0 z.1 a)) →
    fz (e.symm ⟨w, h⟩) c z = fMe w h (L.fT w h t)

end Formalism.L2.Herm

end
end
end

-- Source module: Formalism.LocalToGlobal.HermitianColumns.Lev0Tied

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Lev0Tied (D : D7) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Type :=
  ∀ u, ColLevelX (H.lev0 u) (fun x => x ∈ D.host.K) (aT u).piU (H.vT u)
    (fun v c z => (D.fm u).fv 0 v c ((aT u).pr 0 v c z))

end Formalism.L2.Herm

end
end
end

-- Source module: Formalism.LocalToGlobal.HermitianColumns.ZeroPointScaledByCharacter

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def CofTied (D : D7) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop :=
  ∀ u, D.cOf u * ((aT u).piU : D.host.E) = ((aT D.u₀).piU : D.host.E)

def PiGConst (D : D7) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) (X : Lev0Tied D H aT) : Prop :=
  ∀ u u', (X u).piG = (X u').piG

def stabPLin (D : D7) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) (u : D.what₂.Word)
    (c : (D.fm u).clsP) (s : (D.fm u).stabilizer₂ c) : D.sp.X'.V ≃ₗ[D.host.E] D.sp.X'.V :=
  (toGLb D.sp.X'.frame).symm ((aT u).clsP.stabI c s : GL (Fin D.sp.X'.rank) D.host.E)

def stabMLin (D : D7) (H : HermCols D) (u : D.what₂.Word) (h1 : 1 ≤ D.R.m)
    (c : (D.mem u).C.cls D.R.m) (s : (D.mem u).C.stab D.R.m c) :
    (D.sp.X D.R.m).V ≃ₗ[D.host.E] (D.sp.X D.R.m).V :=
  (toGLb (D.sp.X D.R.m).frame).symm
    ((H.cls u D.R.m h1 le_rfl).stabI c s : GL (Fin (D.sp.X D.R.m).rank) D.host.E)

def StabMapTied (D : D7) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop :=
  ∀ (u : D.what₂.Word) (h1 : 1 ≤ D.R.m) (c : (D.fm u).clsP) (s : (D.fm u).stabilizer₂ c),
    (∀ x : D.sp.X'.V,
      ((aT u).tilG c).1 (stabMLin D H u h1 _ ((D.fm u).stabMap c s) (((aT u).tilG c).1.symm (D.sp.iX' x))) =
        D.sp.iX' (stabPLin D H aT u c s x)) ∧
    ((aT u).tilG c).1 (stabMLin D H u h1 _ ((D.fm u).stabMap c s) (((aT u).tilG c).1.symm (aT u).z0)) = (aT u).z0

def FvStepTied (D : D7) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Type :=
  ∀ (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (v : (D.mem u).A.vT),
    FvTie D.sp.cm (D.sp.X i) (H.lev u i h1 hm).Lb (H.cls u i h1 hm).y (D.clsLat u i) (H.vT u v).1
      ((D.mem u).A.Fv v) (fun c z => (D.fm u).fv i v c ((aT u).pr i v c z))

def RelativeDeterminantCompatible (D : D7) (H : HermTied D) : Prop :=
  ∀ (N : ℕ) (L L' : SDLat D.host.E N), ∀ g ∈ UstdAf D.sp.cm N, Carries g L.1 L'.1 →
    ∀ x : unitaryOneFiniteAdeles D.sp.cm, IsDetOf D.sp.cm x g → D.relDet N L L' = QuotientGroup.mk (H.dt x)

def StdTied (D : D7) : Prop :=
  (∀ i, i ≤ D.R.m → IsStd (D.sp.X i)) ∧ IsStd D.sp.X'

def PositiveVolumeCompatible (D : D7) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → D.sp.Vneg j = false

def BaseTied (D : D7) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop :=
  ∀ (u : D.what₂.Word) (pb : 𝓞 D.host.E), (pb : D.host.E) = D.host.conj ((aT u).piU : D.host.E) →
    ((H.lev0 u).Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 D.host.E)
        (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (H.lev0 u).Lb) = D.sp.crdLat0 (D.sp.X 0).L0) ∧
    ∀ (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m),
      (H.lev u i h1 hm).Lb ⊔ Ideal.span {pb} • dualL D.sp.cm (D.sp.X i) (H.lev u i h1 hm).Lb =
        crdLat (D.sp.X i) (D.sp.X i).L0

end Formalism.L2.Herm

end
end
end
