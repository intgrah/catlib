/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Emily Riehl
-/
module

public import Catlib.CategoryTheory.LocallyCartesianClosed.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Beck-Chevalley natural transformations and natural isomorphisms

We construct the Beck-Chevalley natural transformations and isomorphisms through repeated
applications of the mate construction in the vertical and horizontal directions.

## Main declarations

- `Over.mapIsoSquare`: The isomorphism between the functors `Over.map h ⋙ Over.map g` and
  `Over.map f ⋙ Over.map k` for a commutative square of morphisms `h ≫ g = f ≫ k`.

- `ChosenPullbacksAlong.pullbackMapBeckChevalley`: The Beck-Chevalley natural transformation
  of a commutative square of morphisms `h ≫ g = f ≫ k`.

- `ChosenPullbacksAlong.pullbackIsoSquare`: The isomorphism between the pullbacks along a
  commutative square of morphisms `h ≫ g = f ≫ k`.

- `ChosenPullbacksAlong.pullbackMapIsoSquare`: For a pullback square, the Beck-Chevalley
  transformation is an isomorphism.

- `ExponentiableMorphism.pushforwardPullbackBeckChevalley`: The Beck-Chevalley natural
  transformation between pushforwards and pullbacks of a commutative square.

- `ExponentiableMorphism.pushforwardPullbackIsoSquare`: For a pullback square, the
  pushforward-pullback Beck-Chevalley transformation is an isomorphism.

- `ExponentiableMorphism.pushforwardIsoSquare`: The isomorphism between the pushforwards along
  a commutative square of morphisms `h ≫ g = f ≫ k`.

## Implementation notes

The lax naturality squares are constructed by the mate equivalence `mateEquiv` and the natural
iso-squares are constructed by the more special conjugation equivalence `conjugateIsoEquiv`.

## References

The methodology and the notation of the successive mate constructions to obtain the
Beck-Chevalley natural transformations and isomorphisms are based on the following paper:

* [A 2-categorical proof of Frobenius for fibrations defined from a generic point,
in Mathematical Structures in Computer Science, 2024][Hazratpour_Riehl_2024]

-/

@[expose] public section

namespace CategoryTheory

open Category ChosenPullbacksAlong

universe v u

variable {C : Type u} [Category.{v} C]

namespace Over

theorem map_square_eq {X Y Z W : C} {h : X ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ W} {k : Y ⟶ W}
    (sq : CommSq h f g k) :
    Over.map h ⋙ Over.map g = Over.map f ⋙ Over.map k := by
  rw [← mapComp_eq, sq.w, mapComp_eq]

/-- Promoting the equality `map_square_eq` of functors to an isomorphism.
```
        Over X -- .map h -> Over Z
           |                  |
   .map f  |         ≅        | .map g
           ↓                  ↓
        Over Y -- .map k -> Over W
```
The Beck-Chevalley transformations are iterated mates of this isomorphism in the
horizontal and vertical directions. -/
def mapIsoSquare {X Y Z W : C} {h : X ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ W} {k : Y ⟶ W}
    (sq : CommSq h f g k) :
    Over.map h ⋙ Over.map g ≅ Over.map f ⋙ Over.map k :=
  eqToIso (map_square_eq sq)

end Over

namespace ChosenPullbacksAlong

theorem counit_app_left {X Y : C} (g : Y ⟶ X) [ChosenPullbacksAlong g] (U : Over X) :
    ((mapPullbackAdj g).counit.app U).left = fst U.hom g :=
  rfl

@[reassoc (attr := simp)]
theorem unit_app_left_fst {X Y : C} (g : Y ⟶ X) [ChosenPullbacksAlong g] (B : Over Y) :
    ((mapPullbackAdj g).unit.app B).left ≫ fst ((Over.map g).obj B).hom g = 𝟙 B.left := by
  have h := congrArg CommaMorphism.left ((mapPullbackAdj g).left_triangle_components B)
  simp only [Over.comp_left, Over.map_map_left, Over.id_left] at h
  exact h

variable {X Y Z W : C} (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W)

section

variable [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] (sq : CommSq h f g k)

/-- The Beck-Chevalley natural transformation `pullback f ⋙ map h ⟶ map k ⋙ pullback g`
constructed as a mate of `mapIsoSquare`:
```
    Over Y - pullback f → Over X
      |                     |
map k |          ↙          | map h
      ↓                     ↓
    Over W - pullback g → Over Z
```
-/
def pullbackMapBeckChevalley : pullback f ⋙ Over.map h ⟶ Over.map k ⋙ pullback g :=
  (mateEquiv (mapPullbackAdj f) (mapPullbackAdj g)
    (.mk _ _ _ _ (Over.mapIsoSquare sq).hom)).natTrans

/-- The natural transformation `pullback f ⋙ map h ⟶ map h'` for a triangle `f ≫ h' = h`. -/
def pullbackMapTriangle {X Y Z : C} (f : X ⟶ Y) [ChosenPullbacksAlong f]
    (h : X ⟶ Z) (h' : Y ⟶ Z) (w : f ≫ h' = h) :
    pullback f ⋙ Over.map h ⟶ Over.map h' :=
  (mateEquiv (mapPullbackAdj f) Adjunction.id
    (.mk _ _ _ _ ((Functor.rightUnitor _).hom ≫
      eqToHom (by rw [← w, Over.mapComp_eq])))).natTrans ≫ (Functor.rightUnitor _).hom

/-- The natural transformation `pullback f ⋙ forget X ⟶ forget Y`, the mate of the
isomorphism `mapForget f`. -/
def pullbackForgetTriangle {X Y : C} (f : X ⟶ Y) [ChosenPullbacksAlong f] :
    pullback f ⋙ Over.forget X ⟶ Over.forget Y :=
  (mateEquiv (mapPullbackAdj f) Adjunction.id
    (.mk _ _ _ _ ((Functor.rightUnitor _).hom ≫ (Over.mapForget f).inv))).natTrans ≫
    (Functor.rightUnitor _).hom

variable [ChosenPullbacksAlong h] [ChosenPullbacksAlong k]

/-- The isomorphism between the pullbacks along a commutative square, constructed as the
conjugate of `mapIsoSquare`.
```
          Over X ←--.pullback h-- Over Z
             ↑                       ↑
.pullback f  |          ≅            | .pullback g
             |                       |
          Over Y ←--.pullback k-- Over W
```
-/
def pullbackIsoSquare : pullback k ⋙ pullback f ≅ pullback g ⋙ pullback h :=
  conjugateIsoEquiv ((mapPullbackAdj f).comp (mapPullbackAdj k))
    ((mapPullbackAdj h).comp (mapPullbackAdj g)) (Over.mapIsoSquare sq)

end

section Components

variable {h f g k} [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] (sq : CommSq h f g k)
  (A : Over Y)

@[reassoc (attr := simp)]
theorem pullbackMapBeckChevalley_app_left_fst :
    ((pullbackMapBeckChevalley h f g k sq).app A).left ≫
      fst ((Over.map k).obj A).hom g = fst A.hom f := by
  have h1 := congrArg CommaMorphism.left
    (mateEquiv_counit (mapPullbackAdj f) (mapPullbackAdj g)
      (.mk _ _ _ _ (Over.mapIsoSquare sq).hom) A)
  simp only [Over.comp_left, Over.map_map_left] at h1
  have e : ((Over.mapIsoSquare sq).hom.app ((pullback f).obj A)).left ≫
      ((mapPullbackAdj f).counit.app A).left = fst A.hom f := by
    simp only [Over.mapIsoSquare, eqToIso.hom, eqToHom_app, Over.eqToHom_left]
    exact (id_comp _).trans (counit_app_left f A)
  exact h1.trans e

@[reassoc (attr := simp)]
theorem pullbackMapBeckChevalley_app_left_snd :
    ((pullbackMapBeckChevalley h f g k sq).app A).left ≫
      snd ((Over.map k).obj A).hom g = snd A.hom f ≫ h :=
  Over.w ((pullbackMapBeckChevalley h f g k sq).app A)

/-- The Beck-Chevalley natural transformation of a pullback square is an isomorphism. -/
instance isIso_pullbackMapBeckChevalley (pb : IsPullback h f g k) :
    IsIso (pullbackMapBeckChevalley h f g k pb.toCommSq) := by
  apply (config := { allowSynthFailures := true }) NatIso.isIso_of_isIso_app
  intro A
  suffices hl : IsIso ((pullbackMapBeckChevalley h f g k pb.toCommSq).app A).left by
    have : IsIso ((Over.forget Z).map ((pullbackMapBeckChevalley h f g k pb.toCommSq).app A)) :=
      hl
    exact Functor.ReflectsIsomorphisms.reflects (Over.forget Z) _
  have pbs : IsPullback (fst A.hom f) (snd A.hom f ≫ h) ((Over.map k).obj A).hom g :=
    (isPullback A.hom f).paste_vert pb.flip
  have pbt : IsPullback (fst ((Over.map k).obj A).hom g) (snd ((Over.map k).obj A).hom g)
      ((Over.map k).obj A).hom g := isPullback _ _
  have key : ((pullbackMapBeckChevalley h f g k pb.toCommSq).app A).left =
      (pbs.isoIsPullback _ _ pbt).hom := by
    apply ChosenPullbacksAlong.hom_ext
    · exact (pullbackMapBeckChevalley_app_left_fst pb.toCommSq A).trans
        (pbs.isoIsPullback_hom_fst _ _ pbt).symm
    · exact (pullbackMapBeckChevalley_app_left_snd pb.toCommSq A).trans
        (pbs.isoIsPullback_hom_snd _ _ pbt).symm
  rw [key]
  infer_instance

/-- The pullback-map exchange isomorphism of a pullback square. -/
noncomputable def pullbackMapIsoSquare (pb : IsPullback h f g k) :
    pullback f ⋙ Over.map h ≅ Over.map k ⋙ pullback g :=
  haveI := isIso_pullbackMapBeckChevalley pb
  asIso (pullbackMapBeckChevalley h f g k pb.toCommSq)

end Components

end ChosenPullbacksAlong

namespace ExponentiableMorphism

variable {X Y Z W : C} (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W)
  [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong h]
  [ChosenPullbacksAlong k]

/-- The Beck-Chevalley natural transformation
`pushforward g ⋙ pullback k ⟶ pullback h ⋙ pushforward f` constructed as a conjugate of
`pullbackMapBeckChevalley`.
```
         Over Z - pushforward g → Over W
           |                        |
pullback h |           ↙            | pullback k
           ↓                        ↓
         Over X - pushforward f → Over Y
```
-/
def pushforwardPullbackBeckChevalley (sq : CommSq h f g k)
    [ExponentiableMorphism f] [ExponentiableMorphism g] :
    pushforward g ⋙ pullback k ⟶ pullback h ⋙ pushforward f :=
  conjugateEquiv ((mapPullbackAdj k).comp (pullbackPushforwardAdj g))
    ((pullbackPushforwardAdj f).comp (mapPullbackAdj h))
    (pullbackMapBeckChevalley h f g k sq)

/-- The pushforward-pullback Beck-Chevalley transformation of a pullback square is an
isomorphism. -/
instance isIso_pushforwardPullbackBeckChevalley (pb : IsPullback h f g k)
    [ExponentiableMorphism f] [ExponentiableMorphism g] :
    IsIso (pushforwardPullbackBeckChevalley h f g k pb.toCommSq) := by
  have := ChosenPullbacksAlong.isIso_pullbackMapBeckChevalley pb
  unfold pushforwardPullbackBeckChevalley
  infer_instance

/-- The pullback-pushforward exchange isomorphism of a pullback square: the Beck-Chevalley
condition. -/
noncomputable def pushforwardPullbackIsoSquare (pb : IsPullback h f g k)
    [ExponentiableMorphism f] [ExponentiableMorphism g] :
    pushforward g ⋙ pullback k ≅ pullback h ⋙ pushforward f :=
  haveI := isIso_pushforwardPullbackBeckChevalley h f g k pb
  asIso (pushforwardPullbackBeckChevalley h f g k pb.toCommSq)

/-- The conjugate isomorphism between the pushforwards along a commutative square.
```
            Over X --.pushforward h -→ Over Z
               |                        |
.pushforward f |           ≅            | .pushforward g
               ↓                        ↓
            Over Y --.pushforward k -→ Over W
```
-/
def pushforwardIsoSquare (sq : CommSq h f g k)
    [ExponentiableMorphism f] [ExponentiableMorphism g]
    [ExponentiableMorphism h] [ExponentiableMorphism k] :
    pushforward h ⋙ pushforward g ≅ pushforward f ⋙ pushforward k :=
  conjugateIsoEquiv ((pullbackPushforwardAdj g).comp (pullbackPushforwardAdj h))
    ((pullbackPushforwardAdj k).comp (pullbackPushforwardAdj f))
    (pullbackIsoSquare h f g k sq)

end ExponentiableMorphism

end CategoryTheory
