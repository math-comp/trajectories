import * as THREE from 'three';
import { FontLoader } from 'three/addons/loaders/FontLoader.js';
import { TextGeometry } from 'three/addons/geometries/TextGeometry.js';

const renderer = new THREE.WebGLRenderer();
renderer.setSize( window.innerWidth, window.innerHeight );
document.body.appendChild( renderer.domElement );

const camera = new THREE.PerspectiveCamera( 45, window.innerWidth / window.innerHeight, 1, 500 );
camera.position.set( 0, 0, 10 );
camera.lookAt( 0, 0, 0 );

const scene = new THREE.Scene();
scene.background = new THREE.Color( 'lightgrey' );

//create a blue LineBasicMaterial
const material = new THREE.LineBasicMaterial( { color: 'black' } );
const cmaterial = new THREE.LineBasicMaterial( { color: 'red' } );

/* 
BOTTOM
  ({| left_pt := {| p_x := -4; p_y := -4|};
      right_pt := {| p_x := 4; p_y := -4|}|}).

*/

const bpoints = [];
bpoints.push( new THREE.Vector3( - 4, - 4, 0 ) );
bpoints.push( new THREE.Vector3(   4, - 4, 0 ) );

const bgeometry = new THREE.BufferGeometry().setFromPoints( bpoints );

const bline = new THREE.Line( bgeometry, material );

scene.add( bline );

/* 
Notation TOP :=
  ({| left_pt := {| p_x := -4; p_y := 2|};
      right_pt := {| p_x := 4; p_y := 2|}|}).

*/

const tpoints = [];
tpoints.push( new THREE.Vector3( - 4, 2, 0 ) );
tpoints.push( new THREE.Vector3(   4, 2, 0 ) );

const tgeometry = new THREE.BufferGeometry().setFromPoints( tpoints );

const tline = new THREE.Line( tgeometry, material );

scene.add( tline );

/* 
Definition example_edge_list : seq edge :=
  Bedge (Bpt (-3) 0) (Bpt (-2) 1) ::
  Bedge (Bpt (-3) 0) (Bpt 0 (-3)) ::
  Bedge (Bpt 0 (-3)) (Bpt 3 0) ::
  Bedge (Bpt (-2) 1) (Bpt 0 1) ::
  Bedge (Bpt 0 1) (Bpt 1 0) ::
  Bedge (Bpt (-1) 0) (Bpt 0 (-1)) ::
  Bedge (Bpt 0 (-1)) (Bpt 1 0) :: nil.
*/

const edge_list = [
  {fx : -3, fy : 0, tx : -2, ty : 1},  
  {fx : -3, fy : 0, tx :  0, ty : -3},
  {fx :  0, fy : -3, tx : 3, ty : 0},
  {fx :  -2, fy : 1, tx : 0, ty : 1},
  {fx :  0, fy : 1, tx : 1, ty : 0},
  {fx :  -1, fy : 0, tx : 0, ty : -1},
  {fx :  0, fy : -1, tx : 1, ty : 0}
];

edge_list.forEach(add_edge);

function add_edge(edge) {
  let epoints = [];
  epoints.push( new THREE.Vector3(edge.fx, edge.fy, 0 ) );
  epoints.push( new THREE.Vector3(edge.tx, edge.ty, 0 ) );
  let egeometry = new THREE.BufferGeometry().setFromPoints( epoints );
  let eline = new THREE.Line( egeometry, material );
  scene.add( eline );
}

/* curve
	 = straight {| p_x := -1.9; p_y := -3 # 2 |};
              {| p_x := -19 # 20; p_y := -480 # 192 |} :: 
      bezier  {| p_x := -19 # 20; p_y := -480 # 192 |};
              {| p_x := 0; p_y := -168 # 48 |}
              {| p_x := 3 # 2; p_y := -12672 # 4608 |}; ::
      bezier  {| p_x := 3 # 2; p_y := -12672 # 4608 |};
              {| p_x := 3; p_y := -96 # 48 |}
              {| p_x := 0x3.4%xQ; p_y := -589824 # 393216 |} :: 
      bezier  {| p_x := 0x3.4%xQ; p_y := -589824 # 393216 |}
              {| p_x := 28 # 8; p_y := (-0x1.000)%xQ |}
              {| p_x := 0x3.4%xQ; p_y := 0 # 131072 |}  ::
      bezier  {| p_x := 0x3.4%xQ; p_y := 0 # 131072 |}
              {| p_x := 3; p_y := 0x1.0%xQ |}
              {| p_x := 4 # 2; p_y := 0 # 192 |} ::
      bezier  {| p_x := 4 # 2; p_y := 0 # 192 |}
              {| p_x := 1; p_y := -6 # 6 |}
              {| p_x := 1 # 2; p_y := -36 # 24 |} ::
      bezier  {| p_x := 1 # 2; p_y := -36 # 24 |}
              {| p_x := 0; p_y := -4 # 2 |}
              {| p_x := -1 # 2; p_y := -36 # 24 |}
      bezier  {| p_x := -1 # 2; p_y := -36 # 24 |}
              {| p_x := -1; p_y := -6 # 6 |}
              {| p_x := (-0x1.4)%xQ; p_y := -1080 # 1728 |} ::
      bezier  {| p_x := (-0x1.4)%xQ; p_y := -1080 # 1728 |}
              {| p_x := -12 # 8; p_y := -36 # 144 |}
              {| p_x := (-0x1.4)%xQ; p_y := 144 # 1152 |} ::
      bezier  {| p_x := (-0x1.4)%xQ; p_y := 144 # 1152 |}
              {| p_x := -1; p_y := 2 # 4 |}
              {| p_x := -1 # 2; p_y := 8 # 32 |} ::
      bezier  {| p_x := -1 # 2; p_y := 8 # 32 |};
               ({| p_x := 0; p_y := 0|}).
              {| p_x := 1 # 6; p_y := 0 # 8 |} ::
      straight {| p_x := 1 # 6; p_y := 0 # 8 |};
               {| p_x := 1 # 3; p_y := 0 |};
*/

const curve_list = [
  {b : false, fx : -1.9, fy : -(3/2), tx : -(19/20), ty : - (480 / 192)},  
  {b : true, fx : -(19/20), fy : -(480/192), 
             cx : 0, cy : -(168/48), tx : (3/2), ty : -(12672/4608)},
 {b : true, fx : (3/2), fy : -(12672/4608), 
             cx : 3, cy : -(96/48), tx : (3 + 4/16), ty : -(589824/393216)},
 {b : true, fx : (3 + 4 /16), fy : -(589824/393216), 
             cx : (28/8), cy : -(1), tx : (3 + 4/16), ty : 0},
 {b : true, fx : (3 + 4/16), fy : 0, 
             cx : 3, cy : 1.0, tx : (4/2), ty : 0},
 {b : true, fx : (4/2), fy : 0, 
             cx : 1, cy : -(6/6), tx : (1/2), ty : -(36/24)},
 {b : true, fx : (1/2), fy : -(36/24), 
             cx : 0, cy : -(4/2), tx : -(1/2), ty : -(36/24)},
 {b : true, fx : -(1/2), fy : -(36/24), 
             cx : -1, cy : -(6/6), tx : -(1 + 4 / 16), ty : -(1080/1728)},
 {b : true, fx : -(1 + 4 / 16), fy : -(1080/1728), 
             cx : -(12/8), cy : -(36/144), tx : -(1 + 4/16), ty : (144/1152)},
 {b : true, fx : -(1 + 4 / 16), fy : (144/1152), 
             cx : -1, cy : (2/4), tx : -(1/2), ty : (8/32)},
 {b : true, fx : -(1/2), fy : (8/32), 
             cx : 0, cy : 0, tx : (1/6), ty : 0},
  {b : false, fx : (1/6), fy : 0, tx : (1/3), ty : 0}  
];

curve_list.forEach(add_curve);

function add_curve(curve) {
  if (curve.b) {
    let ccurve = new THREE.QuadraticBezierCurve3(
                	new THREE.Vector3(curve.fx, curve.fy, 0 ),
	                new THREE.Vector3(curve.cx, curve.cy, 0 ),
	                new THREE.Vector3(curve.tx, curve.ty, 0 )
                );
    let cpoints = ccurve.getPoints( 50 );
    let cgeometry = new THREE.BufferGeometry().setFromPoints( cpoints );
    let cline = new THREE.Line( cgeometry, cmaterial );
    scene.add( cline );
  } else {
    let epoints = [];
    epoints.push( new THREE.Vector3(curve.fx, curve.fy, 0 ) );
    epoints.push( new THREE.Vector3(curve.tx, curve.ty, 0 ) );
    let egeometry = new THREE.BufferGeometry().setFromPoints( epoints );
    let sline = new THREE.Line( egeometry, cmaterial );
    scene.add( sline );
  }
}

renderer.render( scene, camera );
