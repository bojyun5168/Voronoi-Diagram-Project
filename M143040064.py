# $LAN=PYTHON$
# -----------------------------------------------------------
# 演算法 Term Project
# 學號：M143040064
# 姓名：曾柏鈞
# -----------------------------------------------------------
import tkinter as tk
import math
from tkinter import filedialog, messagebox

# --- PART 1: 核心資料結構與幾何謂詞 ---

class Point:
    def __init__(self, x, y):
        self.x = int(x)
        self.y = int(y)

    def __sub__(self, other):
        """向量減法 p1 - p2"""
        return Point(self.x - other.x, self.y - other.y)

    def cross(self, other):
        """二維向量外積 (Cross product)"""
        return self.x * other.y - self.y * other.x

    def dot(self, other):
        """向量內積 (Dot product)"""
        return self.x * other.x + self.y * other.y

    def sqrLength(self):
        """向量長度的平方"""
        return self.dot(self)

    def __eq__(self, other):
        """點是否相等"""
        return self.x == other.x and self.y == other.y

    def __lt__(self, other):
        """用於排序：先 x 後 y"""
        return (self.x, self.y) < (other.x, other.y)

    def __repr__(self):
        """方便除錯"""
        return f"Pt({self.x}, {self.y})"

class QuadEdge:
    def __init__(self):
        self.origin = None # 邊的起點 (Point)
        self.rot = None    # 指向 dual 邊 (逆時針)
        self.onext = None  # 指向同一個 face 的下一條邊 (逆時針)
        self.used = False  # 用於圖形遍歷

    def rev(self):
        """返回反向邊 (e.g., B->A)"""
        return self.rot.rot

    def lnext(self):
        """返回左臉 (left face) 的下一條邊"""
        return self.rot.rev().onext.rot

    def oprev(self):
        """返回起點 (origin) 的上一條邊 (逆時針)"""
        return self.rot.onext.rot

    def dest(self):
        """返回這條邊的終點 (Destination)"""
        return self.rev().origin

def make_edge(from_pt, to_pt):
    """
    建立一條邊 e, 包含 e.rev(), e.rot, e.rot.rev()
    總共 4 個 QuadEdge 物件。
    """
    e1 = QuadEdge()
    e2 = QuadEdge()
    e3 = QuadEdge()
    e4 = QuadEdge()

    e1.origin = from_pt
    e2.origin = to_pt
    
    e1.rot = e3
    e2.rot = e4
    e3.rot = e2
    e4.rot = e1

    e1.onext = e1
    e2.onext = e2
    e3.onext = e4
    e4.onext = e3
    
    return e1

def splice(a, b):

    #拓撲操作的核心
    alpha = a.onext.rot
    beta = b.onext.rot

    alpha.onext, beta.onext = beta.onext, alpha.onext
    a.onext, b.onext = b.onext, a.onext

def connect(a, b):

    #建立一條新邊 e，從 a.dest() 到 b.origin()
    e = make_edge(a.dest(), b.origin)
    splice(e, a.lnext())
    splice(e.rev(), b)
    return e

def delete_edge(e):
    #刪除一條邊
    splice(e, e.oprev())
    splice(e.rev(), e.rev().oprev())

# --- 幾何 (Geometric Predicates) ---

def sgn(a):
    #返回數字的符號
    return 1 if a > 0 else -1 if a < 0 else 0

def left_of(p, e):
    #點 p 是否在有向邊 e 的左側
    return (e.dest() - e.origin).cross(p - e.origin) > 0

def right_of(p, e):
    #點 p 是否在有向邊 e 的右側？
    return (e.dest() - e.origin).cross(p - e.origin) < 0

def det3(a1, a2, a3, b1, b2, b3, c1, c2, c3):
    #計算 3x3 行列式 
    return a1 * (b2 * c3 - c2 * b3) - \
           a2 * (b1 * c3 - c1 * b3) + \
           a3 * (b1 * c2 - c1 * b2)

def in_circle(a, b, c, d):
    """
    判斷點 d 是否在 a, b, c 構成的外接圓內部。
    """
    det = -det3(b.x, b.y, b.sqrLength(), c.x, c.y, c.sqrLength(), d.x, d.y, d.sqrLength())
    det += det3(a.x, a.y, a.sqrLength(), c.x, c.y, c.sqrLength(), d.x, d.y, d.sqrLength())
    det -= det3(a.x, a.y, a.sqrLength(), b.x, b.y, b.sqrLength(), d.x, d.y, d.sqrLength())
    det += det3(a.x, a.y, a.sqrLength(), b.x, b.y, b.sqrLength(), c.x, c.y, c.sqrLength())
    return det > 0


# --- PART 2: 分治演算法 ---

def build_tr(points, l, r):
    """
    遞迴建構 Delaunay 三角剖分。
    返回 (ldo, rdo)
    """
    if r - l + 1 == 2:
        # 基例：2 個點
        res = make_edge(points[l], points[r])
        return (res, res.rev())

    if r - l + 1 == 3:
        # 基例：3 個點
        p1, p2, p3 = points[l], points[l+1], points[r]
        a = make_edge(p1, p2)
        b = make_edge(p2, p3)
        splice(a.rev(), b)
        
        sg = sgn((p2 - p1).cross(p3 - p1))
        if sg == 0:
            return (a, b.rev())
        
        c = connect(b, a)
        if sg > 0: # 逆時針
            return (a, b.rev())
        else: # 順時針
            return (c.rev(), c)

    # --- 分治 (Divide) ---
    mid = (l + r) // 2
    ldo, ldi = build_tr(points, l, mid)
    rdi, rdo = build_tr(points, mid + 1, r)

    # --- 合併 (Merge) ---
    while True:
        if left_of(rdi.origin, ldi):
            ldi = ldi.lnext()
        elif right_of(ldi.origin, rdi):
            rdi = rdi.rev().onext
        else:
            break
            
    basel = connect(rdi.rev(), ldi)
    if ldi.origin == ldo.origin:
        ldo = basel.rev()
    if rdi.origin == rdo.origin:
        rdo = basel

    while True:
        lcand = basel.rev().onext
        rcand = basel.oprev()

        valid_lcand = right_of(lcand.dest(), basel)
        if valid_lcand:
            while in_circle(basel.dest(), basel.origin, lcand.dest(), lcand.onext.dest()):
                t = lcand.onext
                delete_edge(lcand)
                lcand = t
        
        valid_rcand = right_of(rcand.dest(), basel)
        if valid_rcand:
            while in_circle(basel.dest(), basel.origin, rcand.dest(), rcand.oprev().dest()):
                t = rcand.oprev()
                delete_edge(rcand)
                rcand = t

        if not valid_lcand and not valid_rcand:
            break

        if not valid_lcand or \
           (valid_rcand and in_circle(lcand.dest(), lcand.origin, rcand.origin, rcand.dest())):
            basel = connect(rcand, basel.rev())
        else:
            basel = connect(basel.rev(), lcand.rev())

    return (ldo, rdo)


# --- PART 3: Duality (VD 實作) 與 GUI ---

class Point_Float:
    """用於繪製的浮點數 Point"""
    def __init__(self, x, y):
        self.x = float(x)
        self.y = float(y)
    
    def dot(self, other):
        """向量內積 (Dot product)"""
        return self.x * other.x + self.y * other.y
    
    def __repr__(self):
        return f"Pt_F({self.x}, {self.y})"

def circumcenter(a, b, c):
    """
    計算 a, b, c 的外接圓心 (用於 Voronoi 頂點)
    """
    ad = a.sqrLength()
    bd = b.sqrLength()
    cd = c.sqrLength()
    
    D = (a.x * (b.y - c.y) + b.x * (c.y - a.y) + c.x * (a.y - b.y)) * 2.0
    if abs(D) < 1e-9: # 共線
        return None

    D_inv = 1.0 / D
    Ux = (ad * (b.y - c.y) + bd * (c.y - a.y) + cd * (a.y - b.y)) * D_inv
    Uy = (ad * (c.x - b.x) + bd * (a.x - c.x) + cd * (b.x - a.x)) * D_inv

    return Point_Float(Ux, Uy)

def calculate_ray_direction(p1, p2, p3):
    """
    計算 Voronoi 射線的方向。
    p1, p2 是 convex hull 邊。
    p3 是這條邊所屬的Delaunay三角形的第三個點。
    射線是 p1, p2 的中垂線，且方向背離 p3。
    """
    # p1, p2 的中點
    mid_point = Point_Float((p1.x + p2.x) * 0.5, (p1.y + p2.y) * 0.5)
    
    # p1->p2 的切線向量 (Tangent)
    T = p2 - p1
    
    # 兩個可能的法線向量 (Normal)
    Dir1 = Point_Float(-T.y, T.x) # 指向 "左"
    Dir2 = Point_Float(T.y, -T.x) # 指向 "右"
    
    # 從中點指向 p3 的向量
    V_mid_p3 = Point_Float(p3.x - mid_point.x, p3.y - mid_point.y)

    if V_mid_p3.dot(Dir1) > 0:
        # Dir1 指向 p3 (內部)，所以我們用 Dir2 (外部)
        return Dir2
    else:
        # Dir1 指向 p3 的反向 (外部)，所以我們用 Dir1
        return Dir1

def extract_diagrams(start_edge):

    delaunay_triangles = []
    voronoi_tmp = []   
    face_circumcenters = {}   
    visited_edges = set()      
    queue = [start_edge]
    
    while queue:
        e = queue.pop(0)
        
        if e in visited_edges:
            continue
        
        visited_edges.add(e)
        visited_edges.add(e.rev())
        
        # --- 1. 處理 e 的左臉 (e.rot) ---
        e_left_face = e.rot
        if e_left_face not in face_circumcenters:
            p1 = e.origin
            p2 = e.dest()
            p3 = e.lnext().dest()
            
            # 使用 sgn 判斷方向
            if sgn((p2 - p1).cross(p3 - p1)) > 0:
                delaunay_triangles.append((p1, p2, p3))
                c_left = circumcenter(p1, p2, p3)
                
                # 修正點：直接存入計算結果 (可能為 None)
                face_circumcenters[e_left_face] = c_left 
                
                queue.append(e.lnext())
                queue.append(e.lnext().lnext())
            else:
                face_circumcenters[e_left_face] = None # 無限 Face
        
        # --- 2. 處理 e 的右臉 (e.rev().rot) ---
        e_right_face = e.rev().rot
        if e_right_face not in face_circumcenters:
            e_rev = e.rev()
            p1 = e_rev.origin
            p2 = e_rev.dest()
            p3 = e_rev.lnext().dest()
            
            if sgn((p2 - p1).cross(p3 - p1)) > 0:
                delaunay_triangles.append((p1, p2, p3))
                c_right = circumcenter(p1, p2, p3)
                
                # 修正點：直接存入計算結果
                face_circumcenters[e_right_face] = c_right

                queue.append(e_rev.lnext())
                queue.append(e_rev.lnext().lnext())
            else:
                face_circumcenters[e_right_face] = None # 無限 Face

        # --- 3. 獲取兩個 face 的外心 ---
        c_left = face_circumcenters.get(e_left_face)
        c_right = face_circumcenters.get(e_right_face)

        # --- 4. 建立 Voronoi 邊 ---
        # 只要不是 None，就是有效點 (處理極遠外心)
        is_left_valid_finite = (c_left is not None)
        is_right_valid_finite = (c_right is not None)
        
        if is_left_valid_finite and is_right_valid_finite:
            # --- 1. 有限邊 ---
            voronoi_tmp.append(("finite", c_left, c_right))
            
        elif is_left_valid_finite and c_right is None:
            # --- 2. 射線 (e 是 hull 邊) ---
            p1 = e.origin
            p2 = e.dest()
            p3 = e.lnext().dest()   
            ray_dir = calculate_ray_direction(p1, p2, p3)
            if ray_dir:
                voronoi_tmp.append(("ray", c_left, ray_dir))
                
        elif c_left is None and is_right_valid_finite:
            # --- 3. 射線 (e.rev() 是 hull 邊) ---
            e_rev = e.rev()
            p1 = e_rev.origin
            p2 = e_rev.dest()
            p3 = e_rev.lnext().dest()   
            ray_dir = calculate_ray_direction(p1, p2, p3)
            if ray_dir:
                voronoi_tmp.append(("ray", c_right, ray_dir))
        
        elif c_left is None and c_right is None:
            # --- 4. 完全共線 (Strictly Collinear) 的補救措施 ---
            # 畫中垂線
            p1 = e.origin
            p2 = e.dest()
            
            if p1 != p2:
                mid_point = Point_Float((p1.x + p2.x) * 0.5, (p1.y + p2.y) * 0.5)
                T = p2 - p1
                Dir1 = Point_Float(-T.y, T.x)
                Dir2 = Point_Float(T.y, -T.x)
                
                voronoi_tmp.append(("ray", mid_point, Dir1))
                voronoi_tmp.append(("ray", mid_point, Dir2))

        # --- 5. 確保共線邊被遍歷 ---
        if e.onext not in visited_edges:
             queue.append(e.onext)
        if e.rev().onext not in visited_edges:
            queue.append(e.rev().onext)


    # --- 轉換射線為長線段以供繪製 ---
    
    diag_length = 1e9 
    
    final_voronoi_lines = []
    for edge in voronoi_tmp:
        if edge[0] == "finite":
            final_voronoi_lines.append((edge[1], edge[2]))
        elif edge[0] == "ray":
            v_start = edge[1]
            v_dir = edge[2]
            norm = math.sqrt(v_dir.dot(v_dir))
            if norm > 1e-9:
                # 這裡計算出的 v_end 會非常遠，但 Clipper 會正確裁切出螢幕內的部分
                v_end = Point_Float(v_start.x + v_dir.x / norm * diag_length,
                                    v_start.y + v_dir.y / norm * diag_length)
                final_voronoi_lines.append((v_start, v_end))

    return delaunay_triangles, final_voronoi_lines

# --- PART 4: 測試案例執行器 ---

class TestCaseRunner:
    """
    管理從檔案讀取測試案例並逐個執行的流程。
    """
    def __init__(self, file_lines, root_window, canvas_widget, next_button_widget, clear_func, recompute_func):
        self.lines = file_lines
        self.root = root_window
        self.canvas = canvas_widget
        self.next_button = next_button_widget
        self.clear_canvas = clear_func # 這是全域的 "手動清除" 函式
        self.recompute_and_draw = recompute_func
        self.line_index = 0
        self.is_running = False

    def _clear_for_next_case(self):
        """
        內部函式：僅清除畫布和資料，不停止測試。
        """
        global input_points, delaunay_tris, voronoi_lines
        input_points = []
        delaunay_tris = []
        voronoi_lines = []
        
        clear_canvas_internal()


    def start(self):
        """開始測試流程"""
        if self.is_running:
            return 
        self.is_running = True
        
        
        print("--- 測試檔案已載入 ---")
        print("請按 'Next Test Case' 按鈕以執行下一個測試案例。")
        

    def stop(self):
        """停止測試流程"""
        if not self.is_running:
            return
        self.is_running = False
        
        if self.next_button:
            self.next_button.config(state="disabled")
        print("--- 測試執行已停止 ---")
        
    def parse_next_case(self):
        """
        從目前行數解析下一個測試案例。
        """
        n = -1
        new_points = []
        
        # 1. 尋找 n (點的數量)
        while self.line_index < len(self.lines):
            line = self.lines[self.line_index].strip()
            self.line_index += 1
            
            if not line or line.startswith('#'):
                continue
            
            try:
                n = int(line)
                break
            except ValueError:
                print(f"警告: 讀取到無效的行 (非數字): {line}")
                continue
        
        if n == -1: # 檔案結束
            return -1, None
            
        if n == 0:
            print("\n=============================")
            print("讀入點數為零，檔案測試停止")
            return 0, None
            
        print(f"\n=============================")
        print(f"讀入資料點數: {n}")
        
        # 2. 讀取 n 個點
        points_read = 0
        while points_read < n and self.line_index < len(self.lines):
            line = self.lines[self.line_index].strip()
            self.line_index += 1
            
            if not line or line.startswith('#'):
                continue
                
            try:
                parts = line.split()
                if len(parts) >= 2:
                    x, y = int(parts[0]), int(parts[1])
                    new_points.append(Point(x, y))
                    print(f"  讀取點 {points_read + 1}: ({x}, {y})")
                    points_read += 1
                else:
                    print(f"警告: 無效的座標行: {line}")
            except Exception:
                print(f"警告: 解析座標時出錯: {line}")
                
        if points_read != n:
            print(f"警告: 應讀取 {n} 個點，但只讀取到 {points_read} 個。")
            
        return n, new_points

    def run_next_case(self, event=None):
        """
        執行下一個測試案例
        """
        global input_points
        
        n, new_points = self.parse_next_case()
        
        if n > 0:
            self._clear_for_next_case()   
            input_points = new_points  
            self.recompute_and_draw() 
        
        elif n == 0:
            self._clear_for_next_case() 
            self.stop()
            
        elif n == -1:
            print("已到達測試檔案結尾。")
            self._clear_for_next_case() 
            self.stop()

# --- PART 4.5: 線段裁切 ---

class LineClipper:
    """
    使用 Cohen-Sutherland 演算法將線段裁切到一個矩形邊界內。
    我們使用 "邏輯" 座標 (Y 軸下往上)。
    """
    def __init__(self, x_min, y_min, x_max, y_max):
        self.x_min = x_min
        self.y_min = y_min
        self.x_max = x_max
        self.y_max = y_max
        
        self.INSIDE = 0  # 0000
        self.LEFT = 1    # 0001
        self.RIGHT = 2   # 0010
        self.BOTTOM = 4  # 0100
        self.TOP = 8     # 1000

    def _compute_outcode(self, x, y):
        """計算一個點的區域碼"""
        code = self.INSIDE
        if x < self.x_min:
            code |= self.LEFT
        elif x > self.x_max:
            code |= self.RIGHT
        if y < self.y_min:
            code |= self.BOTTOM
        elif y > self.y_max:
            code |= self.TOP
        return code

    def clip(self, x1, y1, x2, y2):
        """
        裁切一條線 (x1, y1) 到 (x2, y2)。
        返回 (x1, y1, x2, y2) (浮點數) 或 None (如果完全在外部)。
        """
        outcode1 = self._compute_outcode(x1, y1)
        outcode2 = self._compute_outcode(x2, y2)

        while True:
            if (outcode1 | outcode2) == 0:
                # 1. Trivial accept: 兩個點都在內部
                return x1, y1, x2, y2
            elif (outcode1 & outcode2) != 0:
                # 2. Trivial reject: 兩個點都在同一側的外部
                return None
            else:
                # 3. 需要裁切
                x, y = 0.0, 0.0
                
                # 選擇一個在外部的點
                outcode_out = outcode1 if outcode1 != 0 else outcode2
                
                # 計算交點
                dx = x2 - x1
                dy = y2 - y1
                
                # 避免除以零
                if dx == 0 and dy == 0:
                    return None

                if outcode_out & self.TOP:
                    x = x1 + dx * (self.y_max - y1) / dy if dy != 0 else x1
                    y = self.y_max
                elif outcode_out & self.BOTTOM:
                    x = x1 + dx * (self.y_min - y1) / dy if dy != 0 else x1
                    y = self.y_min
                elif outcode_out & self.RIGHT:
                    y = y1 + dy * (self.x_max - x1) / dx if dx != 0 else y1
                    x = self.x_max
                elif outcode_out & self.LEFT:
                    y = y1 + dy * (self.x_min - x1) / dx if dx != 0 else y1
                    x = self.x_min
                
                # 更新被裁切的點
                if outcode_out == outcode1:
                    x1, y1 = x, y
                    outcode1 = self._compute_outcode(x1, y1)
                else:
                    x2, y2 = x, y
                    outcode2 = self._compute_outcode(x2, y2)

# PART 4.7:  (Stepper) ---

def extract_hull(start_edge):
    """
    從 start_edge 開始遍歷，找出所有構成 Convex Hull 的邊。
    """
    hull_lines = []
    visited_edges = set()
    queue = [start_edge]
    
    while queue:
        e = queue.pop(0)
        if e in visited_edges: continue
        visited_edges.add(e)
        visited_edges.add(e.rev())
        
        # 1. 檢查左臉 (Left Face)
        p1 = e.origin
        p2 = e.dest()
        p3 = e.lnext().dest()
        # 如果 p1->p2->p3 不是逆時針 (面積 <= 0)，代表左邊是外部 (無限)
        if sgn((p2 - p1).cross(p3 - p1)) <= 0:
            hull_lines.append((p1, p2))
            
        # 2. 檢查右臉 (Right Face) -> 即 e.rev() 的左臉
        e_rev = e.rev()
        p1_r = e_rev.origin
        p2_r = e_rev.dest()
        p3_r = e_rev.lnext().dest()
        
        if sgn((p2_r - p1_r).cross(p3_r - p1_r)) <= 0:
            hull_lines.append((p1_r, p2_r))

        # 3. 遍歷鄰居
        if e.onext not in visited_edges: queue.append(e.onext)
        if e.rev().onext not in visited_edges: queue.append(e.rev().onext)
            
    return hull_lines

class DelaunayStepper:
    """
    【包含 Convex Hull (白色虛線) 顯示功能
    """
    def __init__(self, points, root_window):
        self.root = root_window
        self.points = sorted(points)
        self.sub_diagrams = {} # (l, r) -> (ldo, rdo)
        self.action_stack = [] # (type, l, r) or (type, l, mid, r)
        self.mode = 'run'      
        self.is_paused = False
        self.is_finished = False
        
        # --- 狀態機 ---
        self.pause_state = 'idle'
        
        # 視覺化資料緩存
        self.vis_hyperplane = [] # 紅色 Voronoi 切割線
        self.cached_pre_merge_lines = [] # 舊的 Delaunay/Voronoi 線條
        self.cached_pre_merge_hulls = [] # 儲存合併前的 Convex Hull 線段
        self.current_merge_bounds = None 

        if self.points:
            self.push_build(0, len(self.points) - 1)
        else:
            self.is_finished = True

    def push_build(self, l, r):
        if r - l + 1 < 2:  
            return
        self.action_stack.append(('store_result', l, r))
        if r - l + 1 == 2 or r - l + 1 == 3:
            self.action_stack.append(('run_base_case', l, r))
        else:
            mid = (l + r) // 2
            self.action_stack.append(('run_merge', l, mid, r))
            self.action_stack.append(('push_build', mid + 1, r))
            self.action_stack.append(('push_build', l, mid))

    def run(self):
        self.mode = 'run'
        self.is_paused = False
        self.pause_state = 'idle'
        while self.action_stack:
            self.execute_macro_step(force_execute=True)
        if not self.action_stack:
            self.is_finished = True
            print("--- 演算法執行完畢 ---")

    def step(self):
        self.mode = 'step'
        self.is_paused = False
        self.pause_state = 'idle'
        while self.action_stack:
            pause_reached = self.execute_macro_step(force_execute=False)
            if pause_reached: break 
        if not self.action_stack:
            self.is_finished = True
            print("--- 演算法執行完畢 ---")

    def execute_macro_step(self, force_execute):
        if not self.action_stack: return False
        action = self.action_stack.pop()
        act_type = action[0]

        if act_type == 'push_build':
            self.push_build(action[1], action[2])
            return False
        
        elif act_type == 'run_base_case':
            l, r = action[1], action[2]
            self.sub_diagrams[(l, r)] = build_tr(self.points, l, r) 
            return False
        
        elif act_type == 'run_merge':
            l, mid, r = action[1], action[2], action[3]
            if force_execute:
                self._execute_merge_step(l, mid, r)
                return False
            else:
                # --- Step 3.1: 準備合併 ---
                self.is_paused = True
                self.pause_state = 'at_merge_3_1'
                self.action_stack.append(action)
                self.current_merge_bounds = (l, r)
                
                # 1. 取得子圖
                ldo, _ = self.sub_diagrams[(l, mid)]
                _, rdo = self.sub_diagrams[(mid + 1, r)]
                
                # 2. 快取舊線條
                _, lines_left = extract_diagrams(ldo)
                _, lines_right = extract_diagrams(rdo)
                self.cached_pre_merge_lines = [('blue', lines_left), ('yellow', lines_right)]
                
                # 3. 【*新*】 計算合併前的 Convex Hull (左 + 右)
                hull_left = extract_hull(ldo)
                hull_right = extract_hull(rdo)
                self.cached_pre_merge_hulls = hull_left + hull_right
                
                self.vis_hyperplane = []
                self.draw_merging_state(state='pre_merge')
                print(f"--- 暫停 (3.1): 準備合併 [{l}, {mid}] 和 [{mid+1}, {r}] ---")
                return True 

        elif act_type == 'store_result':
            l, r = action[1], action[2]
            if (l,r) == (0, len(self.points)-1):
                ldo, rdo = self.sub_diagrams[(l,r)]
                self.draw_final(ldo) 
            return False
        return False

    def _get_bisector_ray(self, p1, p2):
        mid = Point_Float((p1.x + p2.x) * 0.5, (p1.y + p2.y) * 0.5)
        dx = p2.x - p1.x
        dy = p2.y - p1.y
        nx, ny = -dy, dx
        length = math.hypot(nx, ny)
        if length < 1e-9: return mid, Point_Float(0, 1)
        nx /= length
        ny /= length
        return mid, Point_Float(nx, ny)

    def _execute_merge_step(self, l, mid, r):
        print("  Merge: 執行中...")
        self.vis_hyperplane = []
        ldo, ldi = self.sub_diagrams[(l, mid)]
        rdi, rdo = self.sub_diagrams[(mid + 1, r)]

        # Find Lower Tangent
        while True:
            if left_of(rdi.origin, ldi): ldi = ldi.lnext()
            elif right_of(ldi.origin, rdi): rdi = rdi.rev().onext
            else: break
        
        basel = connect(rdi.rev(), ldi)
        if ldi.origin == ldo.origin: ldo = basel.rev()
        if rdi.origin == rdo.origin: rdo = basel

        # Hyperplane Start
        mid_start, _ = self._get_bisector_ray(basel.origin, basel.dest())
        dx, dy = basel.dest().x - basel.origin.x, basel.dest().y - basel.origin.y
        up_x, up_y = dy, -dx 
        norm = math.hypot(up_x, up_y)
        if norm > 1e-9: up_x /= norm; up_y /= norm
        else: up_x, up_y = 0, 1
        current_v_node = Point_Float(mid_start.x - up_x * 4000.0, mid_start.y - up_y * 4000.0)
        
        # Merge Loop
        while True:
            lcand = basel.rev().onext
            rcand = basel.oprev()
            valid_lcand = right_of(lcand.dest(), basel)
            if valid_lcand:
                while in_circle(basel.dest(), basel.origin, lcand.dest(), lcand.onext.dest()):
                    t = lcand.onext
                    delete_edge(lcand)
                    lcand = t
            valid_rcand = right_of(rcand.dest(), basel)
            if valid_rcand:
                while in_circle(basel.dest(), basel.origin, rcand.dest(), rcand.oprev().dest()):
                    t = rcand.oprev()
                    delete_edge(rcand)
                    rcand = t

            if not valid_lcand and not valid_rcand: break

            next_v_node = None
            if not valid_lcand or (valid_rcand and in_circle(lcand.dest(), lcand.origin, rcand.origin, rcand.dest())):
                next_v_node = circumcenter(basel.origin, basel.dest(), rcand.dest())
                basel = connect(rcand, basel.rev())
            else:
                next_v_node = circumcenter(basel.origin, basel.dest(), lcand.dest())
                basel = connect(basel.rev(), lcand.rev())
            
            if next_v_node:
                self.vis_hyperplane.append((current_v_node, next_v_node))
                current_v_node = next_v_node
            else:
                mid_pt, _ = self._get_bisector_ray(basel.origin, basel.dest())
                self.vis_hyperplane.append((current_v_node, mid_pt))
                current_v_node = mid_pt

        # Hyperplane End
        dx, dy = basel.dest().x - basel.origin.x, basel.dest().y - basel.origin.y
        up_x, up_y = dy, -dx
        norm = math.hypot(up_x, up_y)
        if norm > 1e-9: up_x /= norm; up_y /= norm
        final_node = Point_Float(current_v_node.x + up_x * 4000.0, current_v_node.y + up_y * 4000.0)
        self.vis_hyperplane.append((current_v_node, final_node))

        self.sub_diagrams[(l, r)] = (ldo, rdo)
        print("  Merge: 完成")

    def draw_merging_state(self, state):
        clear_canvas_internal()
        # 取得當前處理的範圍 [l, r]
        l_bound, r_bound = -1, -1
        if self.current_merge_bounds:
            l_bound, r_bound = self.current_merge_bounds
            
        # 遍歷所有點，根據索引 i 判斷是否在範圍內
        for i, p in enumerate(self.points):
            draw_y = window_height - p.y
            
            if l_bound <= i <= r_bound:
                # 處理中的點：亮綠色 (#00ff00)，稍微畫大一點 (半徑4)
                canvas.create_oval(p.x - 4, draw_y - 4, p.x + 4, draw_y + 4, fill="#00ff00", outline="#00ff00")
            else:
                # 非處理中的點：紅色，正常大小 (半徑3)
                canvas.create_oval(p.x - 3, draw_y - 3, p.x + 3, draw_y + 3, fill="red", outline="red")
        
        def draw_lines(lines, color, width=1.5, dash=None):
            for (v1, v2) in lines:
                if v1 is None or v2 is None: continue
                p1_x, p1_y = v1.x, v1.y
                p2_x, p2_y = v2.x, v2.y
                clipped = clipper.clip(p1_x, p1_y, p2_x, p2_y)
                if clipped:
                    cx1, cy1, cx2, cy2 = clipped
                    kwargs = {"fill": color, "width": width}
                    if dash: kwargs["dash"] = dash
                    canvas.create_line(cx1, window_height - cy1, cx2, window_height - cy2, **kwargs)

        if state == 'pre_merge' or state == 'merged_overlay':
            for color, lines in self.cached_pre_merge_lines:
                draw_lines(lines, color)
            draw_lines(self.cached_pre_merge_hulls, "white", width=2.0, dash=(5, 5))

        if state == 'merged_overlay':
            draw_lines(self.vis_hyperplane, "red", width=2.5)

        if state == 'post_merge':
            l, r = self.current_merge_bounds
            if (l, r) in self.sub_diagrams:
                ldo, _ = self.sub_diagrams[(l, r)]
                _, new_lines = extract_diagrams(ldo)
                draw_lines(new_lines, "red", width=1.5)
                new_hull = extract_hull(ldo)
                draw_lines(new_hull, "white", width=2.0, dash=(5, 5))
        canvas.update()

    def draw_final(self, final_outer_edge):
        clear_canvas_internal()
        global input_points, voronoi_lines, delaunay_tris
        input_points = self.points
        delaunay_tris, voronoi_lines = extract_diagrams(final_outer_edge)
        
        final_hull = extract_hull(final_outer_edge)

        for p in self.points:
            draw_y = window_height - p.y  
            canvas.create_oval(p.x - 3, draw_y - 3, p.x + 3, draw_y + 3, fill="red", outline="red")
        
        # Delaunay (隱藏)
        for (p1, p2, p3) in delaunay_tris:
            canvas.create_polygon(p1.x, window_height - p1.y, p2.x, window_height - p2.y, p3.x, window_height - p3.y, fill="", outline="#222222", width=1)
        
        # 最終 Convex Hull (白色虛線)
        for (v1, v2) in final_hull:
            clipped = clipper.clip(v1.x, v1.y, v2.x, v2.y)
            if clipped:
                 canvas.create_line(clipped[0], window_height - clipped[1], clipped[2], window_height - clipped[3], fill="white", width=2.0, dash=(5, 5))

        # 最終 Voronoi (淺藍)
        for (v1, v2) in voronoi_lines:
            if v1 is None or v2 is None: continue
            clipped = clipper.clip(v1.x, v1.y, v2.x, v2.y)
            if clipped:
                canvas.create_line(clipped[0], window_height - clipped[1], clipped[2], window_height - clipped[3], fill="cyan", width=1.5)

# --- PART 5: Tkinter GUI ---

input_points = []
delaunay_tris = []
voronoi_lines = [] 
window_width = 800
window_height = 600

# --- 全域狀態變數 ---
test_runner = None     # 用於 "Load Test File"
g_stepper = None       # 用於 "Run" / "Step"

clipper = LineClipper(0, 0, window_width, window_height)

def clear_canvas_internal():
    """僅清除畫布和全域變數，不停止 stepper"""
    global input_points, delaunay_tris, voronoi_lines
    canvas.delete("all")
    input_points = []
    delaunay_tris = []
    voronoi_lines = []

def clear_canvas(event=None):
    """
    完全重置，停止所有正在進行的計算。
    """
    global g_stepper, test_runner
    
    # 停止 "Load Test File" 流程
    if test_runner and test_runner.is_running:
        test_runner.stop()
        print("手動清除，測試已停止。")
    test_runner = None
    test_case_button.config(text="Next Test Case", state="disabled") # 重置按鈕
    
    # 停止 "Run"/"Step" 流程
    if g_stepper:
        g_stepper.mode = 'stop' # 告訴 run_loop 停止
        g_stepper.is_finished = True
        g_stepper = None
        print("手動清除，計算已停止。")
        
    clear_canvas_internal()

def on_mouse_click(event):
    """
    點擊畫布：新增一個點。
    如果正在計算，會停止並重置。
    如果已有計算結果，會清除舊線條，保留點。
    """
    global g_stepper, test_runner, input_points, delaunay_tris, voronoi_lines
    
    if event.y >= 0 and event.y < 40:
        return

    is_computing = (g_stepper and not g_stepper.is_finished)
    is_testing = (test_runner and test_runner.is_running)

    if is_computing or is_testing:
        print("手動點擊，停止目前計算並重置點。")
        clear_canvas(event) 
        
    elif (g_stepper and g_stepper.is_finished) or delaunay_tris or voronoi_lines:
        print("手動點擊，清除舊的計算結果。")
        g_stepper = None
        delaunay_tris = []
        voronoi_lines = []
        
        canvas.delete("all")
        for p in input_points:
            draw_y = window_height - p.y  
            canvas.create_oval(p.x - 3, draw_y - 3, p.x + 3, draw_y + 3, fill="red", outline="red")
            
    logical_y = window_height - event.y  
    new_point = Point(event.x, logical_y)
    input_points.append(new_point)
    
    draw_y = window_height - logical_y  
    canvas.create_oval(event.x - 3, draw_y - 3, event.x + 3, draw_y + 3, fill="red", outline="red")
    
    print(f"已新增點: ({new_point.x}, {new_point.y})。目前共 {len(input_points)} 個點。")
    print("請按 'Run' 或 'Step' 開始計算。")


def load_test_file():
    """
    載入測試檔案，並使用 TestCaseRunner 逐步載入
    """
    global test_runner, g_stepper
    
    clear_canvas()
        
    filepath = filedialog.askopenfilename(
        title="選擇 Voronoi 測試資料檔案",
        filetypes=(("Text files", "*.txt"), ("All files", "*.*"))
    )
    if not filepath: return 
        
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            lines = f.readlines()
            
        test_runner = TestCaseRunner(
            lines,
            root,                
            canvas,              
            test_case_button, 
            clear_canvas,        
            None 
        )
        
        test_runner.run_next_case = run_next_test_case_and_pause
        test_runner.start() 
        
        test_case_button.config(text="Next Test Case", state="normal", command=test_runner.run_next_case)
        print("測試檔案已載入。請點擊 'Next Test Case'。")
        
    except Exception as e:
        print(f"讀取檔案時出錯: {e}")
        messagebox.showerror("檔案錯誤", f"無法讀取檔案: {e}")

def run_next_test_case_and_pause():
    global input_points, test_runner, g_stepper
    
    if not test_runner: 
        print("Test runner is None, cannot run next case.")
        return

    clear_canvas_internal() 
    
    if g_stepper:
        g_stepper.is_finished = True
        g_stepper = None
    
    n, new_points = test_runner.parse_next_case()
    
    if n > 0:
        input_points = new_points
        
        for p in input_points:
            draw_y = window_height - p.y  
            canvas.create_oval(p.x - 3, draw_y - 3, p.x + 3, draw_y + 3, fill="red", outline="red")
        
        print("點已載入。請按 'Run' 或 'Step' 開始計算。")
        
    elif n == 0 or n == -1:
        test_case_button.config(text="No Test Case", state="disabled")
        test_runner.stop()
        if n == -1: print("已到達檔案結尾。")


def start_computation(mode):
    """
    根據 'input_points' 啟動一個新的 Stepper 計算
    """
    global g_stepper
    
    if g_stepper and not g_stepper.is_finished:
        print("警告: 清除上一個尚未完成的計算。")
        g_stepper.is_finished = True
    g_stepper = None 
    
    if not input_points:
        print("沒有點可供計算。")
        return

    g_stepper = DelaunayStepper(input_points, root)
    
    if mode == 'run':
        print("--- 'Run' 模式啟動 ---")
        g_stepper.run()
    else: # 'step'
        print("--- 'Step' 模式啟動 ---")
        g_stepper.step()

def on_run_button():
    """ 'Run' 按鈕的邏輯 (阻塞)"""
    global g_stepper
    if g_stepper and (g_stepper.is_paused or not g_stepper.is_finished):
        print("--- 'Run' 模式繼續 (阻塞) ---")
        g_stepper.run()
    else:
        start_computation('run')

def on_step_button():
    """ 'Step' 按鈕的邏輯 (3.1 -> 3.2 -> 3.3 -> Next)"""
    global g_stepper
    
    if g_stepper is None or g_stepper.is_finished:
        start_computation('step')
        
    elif g_stepper.pause_state == 'at_merge_3_1':
        # --- 當前: 3.1 (已顯示分開的舊圖) ---
        # --- 動作: 執行合併，進入 3.2 (顯示舊圖 + Hyperplane) ---
        print("--- (3.2) 繪製 Hyperplane (線條尚未消除) ---")
        
        # 1. 執行運算
        action = g_stepper.action_stack.pop() 
        l, mid, r = action[1], action[2], action[3]
        g_stepper._execute_merge_step(l, mid, r)
        
        # 2. 切換狀態 -> 3.2
        g_stepper.pause_state = 'at_merge_3_2'
        g_stepper.draw_merging_state(state='merged_overlay')
        
    elif g_stepper.pause_state == 'at_merge_3_2':
        # --- 當前: 3.2 (舊圖 + Hyperplane) ---
        # --- 動作: 消除多餘線條，進入 3.3 (新圖 + Hyperplane) ---
        print("--- (3.3) 消除多餘線條 ---")
        
        # 1. 切換狀態 -> 3.3
        g_stepper.pause_state = 'at_merge_3_3'
        g_stepper.draw_merging_state(state='post_merge')
        
        # 準備好繼續
        g_stepper.is_paused = False 
        
    elif g_stepper.pause_state == 'at_merge_3_3' or g_stepper.pause_state == 'idle':
        # --- 當前: 3.3 (已消除) 或 Idle ---
        # --- 動作: 繼續執行下一個巨集 ---
        g_stepper.pause_state = 'idle'
        if g_stepper.is_paused: g_stepper.is_paused = False
        g_stepper.step()

# --- 載入和儲存 ---

def load_and_draw_result():
    clear_canvas()
    filepath = filedialog.askopenfilename(
        title="載入 Voronoi 結果檔案 (P/E 格式)",
        filetypes=(("Text files", "*.txt"), ("All files", "*.*"))
    )
    if not filepath: return
    parsed_points = []
    parsed_edges = []
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            for line in f:
                parts = line.strip().split()
                if not parts: continue
                if parts[0] == 'P' and len(parts) >= 3:
                    parsed_points.append(Point(int(parts[1]), int(parts[2])))
                elif parts[0] == 'E' and len(parts) >= 5:
                    parsed_edges.append((int(parts[1]), int(parts[2]), int(parts[3]), int(parts[4])))
    except Exception as e:
        messagebox.showerror("檔案讀取錯誤", f"無法讀取或解析檔案: {e}")
        return

    for p in parsed_points:
        draw_y = window_height - p.y
        canvas.create_oval(p.x - 3, draw_y - 3, p.x + 3, draw_y + 3, fill="red", outline="red")
    for (x1, y1, x2, y2) in parsed_edges:
        canvas.create_line(x1, window_height - y1, x2, window_height - y2, fill="cyan", width=1.5)
        
    global input_points
    input_points = parsed_points
    print(f"已載入並繪製結果: {filepath}")

def save_results():
    global input_points, voronoi_lines, clipper
    
    if not input_points:
        messagebox.showinfo("無資料", "沒有輸入點，無法儲存。")
        return
    if not voronoi_lines:
        messagebox.showinfo("無資料", "沒有計算結果的線段，無法儲存。\n(請先 'Run' 或 'Step' 完成計算。)")
        return

    filepath = filedialog.asksaveasfilename(
        title="儲存 Voronoi 結果",
        filetypes=(("Text files", "*.txt"), ("All files", "*.*")),
        defaultextension=".txt"
    )
    if not filepath: return 

    final_lines_set = set()
    for (v1, v2) in voronoi_lines:
        if v1 is None or v2 is None: continue
        clipped_segment = clipper.clip(v1.x, v1.y, v2.x, v2.y)
        if clipped_segment:
            x1_f, y1_f, x2_f, y2_f = clipped_segment
            x1_r, y1_r = int(round(x1_f)), int(round(y1_f))
            x2_r, y2_r = int(round(x2_f)), int(round(y2_f))
            if (x1_r, y1_r) > (x2_r, y2_r):
                x1_r, y1_r, x2_r, y2_r = x2_r, y2_r, x1_r, y1_r
            if (x1_r, y1_r) == (x2_r, y2_r): continue
            final_lines_set.add((x1_r, y1_r, x2_r, y2_r))

    sorted_points = sorted(input_points)
    sorted_lines = sorted(list(final_lines_set))

    try:
        with open(filepath, 'w', encoding='utf-8') as f:
            for p in sorted_points: f.write(f"P {p.x} {p.y}\n")
            for (x1, y1, x2, y2) in sorted_lines: f.write(f"E {x1} {y1} {x2} {y2}\n")
        messagebox.showinfo("成功", "結果已成功儲存。")
    except Exception as e:
        messagebox.showerror("儲存錯誤", f"儲存檔案失敗: {e}")

# --- 主程式：設定 GUI ---
root = tk.Tk()
root.title("Python Voronoi & Delaunay (Guibas-Stolfi) - Stepper Mode")

control_frame = tk.Frame(root)
control_frame.pack(side="top", fill="x", pady=5)

# --- 按鈕定義 ---
clear_button = tk.Button(control_frame, text="Clear All", command=clear_canvas)
clear_button.pack(side="left", padx=5)

load_test_button = tk.Button(control_frame, text="Load Test File", command=load_test_file)
load_test_button.pack(side="left", padx=5)

test_case_button = tk.Button(control_frame, text="Next Test Case", state="disabled")
test_case_button.pack(side="left", padx=5)

run_button = tk.Button(control_frame, text="Run", command=on_run_button, bg="#aaffaa")
run_button.pack(side="left", padx=5)

step_button = tk.Button(control_frame, text="Step", command=on_step_button, bg="#aaaaff")
step_button.pack(side="left", padx=5)

save_button = tk.Button(control_frame, text="Save Results", command=save_results)
save_button.pack(side="left", padx=5)

load_result_button = tk.Button(control_frame, text="Load Result (Draw)", command=load_and_draw_result)
load_result_button.pack(side="left", padx=5)

# --- 畫布 ---
canvas = tk.Canvas(root, width=window_width, height=window_height, bg="#222222")
canvas.pack()

canvas.bind("<Button-1>", on_mouse_click)

print("GUI 已啟動。 (Y 軸下往上)")
print("1. 點擊畫布以新增點。")
print("2. 點擊 'Load Test File'，然後 'Next Test Case' 來載入點。")
print("3. 載入點後，點擊 'Run' (一次完成) 或 'Step' (分步) 開始計算。")
root.mainloop()