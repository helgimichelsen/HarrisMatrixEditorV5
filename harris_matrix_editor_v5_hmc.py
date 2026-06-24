
import json, csv, re, xml.etree.ElementTree as ET
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog
from pathlib import Path
from collections import defaultdict, deque

APP_TITLE = "Harris Matrix Editor 5.0 HMC"
TYPE_COLORS = {
    "Deposit":"#9FC4E8",      # HMC-like blue units
    "Surface":"#8AD37D",      # HMC-like green interfaces/surfaces
    "Cut":"#E88B8B",
    "Fill":"#F2B66D",
    "Structural":"#9FC4E8",
    "Natural":"#D8D8D8",
    "Top":"#8AD37D",
    "Geology":"#8AD37D",
    "Unexcavated":"#BDBDBD",
    "Same context":"#F3B6C4",
    "Unknown":"#EFEFEF",
}
BOX_W, BOX_H = 112, 42

REL_STRAT = "stratigraphic"
REL_LATER = "later"
REL_CONTEMP = "contemporary"

def esc(s):
    return str(s).replace("&","&amp;").replace("<","&lt;").replace(">","&gt;")

class HarrisApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_TITLE)
        self.geometry("1520x950")
        self.nodes = {}
        self.edges = []   # {source,target,type}
        self.groups = []  # {id,name,type,collapsed,x,y,w,h,members}
        self.bookmarks = []
        self.selected = None
        self.selected_group = None
        self.drag = (0,0)
        self.resize_group = False
        self.move_group = False
        self.filename = None
        self.zoom = 1.0
        self.show_temporal = tk.BooleanVar(value=True)
        self.show_groups = tk.BooleanVar(value=True)
        self.status = tk.StringVar(value="Klar")
        self._ui()
        self.new_minimal_matrix()

    def _ui(self):
        toolbar = tk.Frame(self); toolbar.pack(fill=tk.X)
        buttons = [
            ("Ny HMC", self.new_minimal_matrix), ("Åbn JSON", self.open_json), ("Gem", self.save_json),
            ("Import HMCX", self.import_hmcx), ("Eksport HMCX", self.export_hmcx),
            ("Import tekst", self.import_rel_text), ("Eksport PDF", self.export_pdf), ("Eksport SVG", self.export_svg),
            ("Deposit", lambda:self.add_node_dialog("Deposit")), ("Surface", lambda:self.add_node_dialog("Surface")),
            ("Relation above", self.add_edge_dialog), ("Later", self.add_later_dialog), ("Contemporary", self.add_contemporary_dialog),
            ("Phase", lambda:self.add_group_dialog("Phase")), ("Period", lambda:self.add_group_dialog("Period")),
            ("Collapse/Expand", self.toggle_group), ("Auto-layout", self.auto_layout), ("Validity check", self.validate_show),
            ("Search", self.search_dialog), ("Bookmark", self.add_bookmark), ("Go bookmark", self.goto_bookmark),
            ("Zoom +", lambda:self.set_zoom(self.zoom*1.15)), ("Zoom -", lambda:self.set_zoom(self.zoom/1.15)), ("Fit", self.fit_view)
        ]
        for t,c in buttons:
            tk.Button(toolbar,text=t,command=c).pack(side=tk.LEFT,padx=1,pady=2)
        tk.Checkbutton(toolbar,text="Temporal",variable=self.show_temporal,command=self.draw).pack(side=tk.LEFT)
        tk.Checkbutton(toolbar,text="Groups",variable=self.show_groups,command=self.draw).pack(side=tk.LEFT)

        main = tk.PanedWindow(self, orient=tk.HORIZONTAL)
        main.pack(fill=tk.BOTH, expand=True)

        left = tk.Frame(main)
        main.add(left, stretch="always")
        self.canvas = tk.Canvas(left, bg="white", scrollregion=(0,0,3200,2400))
        self.canvas.pack(side=tk.LEFT,fill=tk.BOTH,expand=True)
        y = tk.Scrollbar(left,orient=tk.VERTICAL,command=self.canvas.yview); y.pack(side=tk.RIGHT,fill=tk.Y)
        x = tk.Scrollbar(left,orient=tk.HORIZONTAL,command=self.canvas.xview); x.pack(side=tk.BOTTOM,fill=tk.X)
        self.canvas.configure(yscrollcommand=y.set,xscrollcommand=x.set)

        right = tk.Frame(main, width=310)
        main.add(right)
        tk.Label(right,text="Properties",font=("Arial",12,"bold")).pack(anchor="w",padx=4,pady=3)
        self.prop = tk.Text(right,height=11,width=38)
        self.prop.pack(fill=tk.X,padx=4)
        tk.Button(right,text="Update selected properties",command=self.update_props_from_panel).pack(fill=tk.X,padx=4,pady=2)

        tk.Label(right,text="Relations editor",font=("Arial",12,"bold")).pack(anchor="w",padx=4,pady=3)
        self.relations_list = tk.Listbox(right,height=12)
        self.relations_list.pack(fill=tk.BOTH,expand=True,padx=4)
        tk.Button(right,text="Delete selected relation",command=self.delete_selected_relation).pack(fill=tk.X,padx=4,pady=2)

        tk.Label(right,text="Search results / Bookmarks",font=("Arial",12,"bold")).pack(anchor="w",padx=4,pady=3)
        self.search_list = tk.Listbox(right,height=8)
        self.search_list.pack(fill=tk.BOTH,expand=True,padx=4)
        self.search_list.bind("<Double-Button-1>", self.goto_search_result)

        tk.Label(self,textvariable=self.status,anchor="w").pack(fill=tk.X)

        self.canvas.bind("<ButtonPress-1>", self.press)
        self.canvas.bind("<B1-Motion>", self.motion)
        self.canvas.bind("<ButtonRelease-1>", self.release)
        self.canvas.bind("<Double-Button-1>", self.double)
        self.canvas.bind("<MouseWheel>", self.on_mousewheel)

    def sx(self,x): return x*self.zoom
    def sy(self,y): return y*self.zoom
    def ux(self,x): return x/self.zoom
    def uy(self,y): return y/self.zoom

    def new_minimal_matrix(self):
        self.nodes = {
            "Top": {"id":"Top","label":"Top surface","type":"Top","x":540,"y":40,"w":130},
            "Unexcavated": {"id":"Unexcavated","label":"Unexcavated","type":"Unexcavated","x":520,"y":380,"w":165},
            "Geology": {"id":"Geology","label":"Interface to geology","type":"Geology","x":500,"y":520,"w":205},
        }
        self.edges = [
            {"source":"Top","target":"Unexcavated","type":REL_STRAT},
            {"source":"Unexcavated","target":"Geology","type":REL_STRAT},
        ]
        self.groups=[]; self.bookmarks=[]; self.selected=None; self.selected_group=None
        self.draw(); self.status.set("Minimal valid HMC matrix created")

    def draw(self):
        self.canvas.delete("all")
        # groups/periods/phases
        if self.show_groups.get():
            for i,g in enumerate(self.groups):
                if g.get("collapsed"):
                    col="#EDEDED" if g.get("type")=="Phase" else "#F6F1DC"
                    self.canvas.create_rectangle(self.sx(g["x"]),self.sy(g["y"]),self.sx(g["x"]+110),self.sy(g["y"]+40),fill=col,outline="#666",width=2,tags=("group",str(i)))
                    self.canvas.create_text(self.sx(g["x"]+55),self.sy(g["y"]+20),text=g.get("name","Group"),font=("Arial",9,"bold"),tags=("group",str(i)))
                else:
                    outline = "red" if i==self.selected_group else ("#666" if g.get("type")=="Period" else "#4B7DBA")
                    fill = "" 
                    self.canvas.create_rectangle(self.sx(g["x"]),self.sy(g["y"]),self.sx(g["x"]+g["w"]),self.sy(g["y"]+g["h"]),outline=outline,dash=(6,4),width=2,tags=("group",str(i)))
                    self.canvas.create_text(self.sx(g["x"]+8),self.sy(g["y"]+16),text=f"{g.get('type','Group')}: {g.get('name','')}",anchor="w",fill=outline,font=("Arial",10,"bold"),tags=("group",str(i)))
                    self.canvas.create_rectangle(self.sx(g["x"]+g["w"]-10),self.sy(g["y"]+g["h"]-10),self.sx(g["x"]+g["w"]+2),self.sy(g["y"]+g["h"]+2),fill=outline,outline="",tags=("gresize",str(i)))
        # edges
        for e in self.edges:
            if e["source"] in self.nodes and e["target"] in self.nodes:
                if e.get("type") != REL_STRAT and not self.show_temporal.get(): continue
                self.draw_edge(self.nodes[e["source"]], self.nodes[e["target"]], e.get("type",REL_STRAT))
        # nodes
        hidden = set()
        for g in self.groups:
            if g.get("collapsed"):
                hidden.update(g.get("members",[]))
        for n in self.nodes.values():
            if n["id"] not in hidden:
                self.draw_node(n)
        self.legend()
        self.update_side_panel()

    def draw_node(self,n):
        x,y,w,h = self.sx(n["x"]), self.sy(n["y"]), self.sx(n.get("w",BOX_W)), self.sy(n.get("h",BOX_H))
        col = TYPE_COLORS.get(n.get("type","Unknown"), TYPE_COLORS["Unknown"])
        shape = n.get("type")
        outline = "red" if n["id"] == self.selected else "black"
        if shape in ("Surface","Top","Geology"):
            self.canvas.create_oval(x,y,x+w,y+h,fill=col,outline=outline,width=2,tags=("node",n["id"]))
        else:
            self.canvas.create_rectangle(x,y,x+w,y+h,fill=col,outline=outline,width=2,tags=("node",n["id"]))
        self.canvas.create_text(x+w/2,y+h/2,text=n.get("label",n["id"]),font=("Arial",9,"bold"),tags=("node",n["id"]))
        if n.get("invalid"):
            self.canvas.create_text(x+w+7,y+h/2,text="!",fill="red",font=("Arial",14,"bold"))

    def draw_edge(self,a,b,typ):
        aw,ah=a.get("w",BOX_W),a.get("h",BOX_H); bw,bh=b.get("w",BOX_W),b.get("h",BOX_H)
        x1,y1=a["x"]+aw/2,a["y"]+ah
        x2,y2=b["x"]+bw/2,b["y"]
        if typ == REL_CONTEMP:
            y=(a["y"]+b["y"]+BOX_H/2)/2
            self.canvas.create_line(self.sx(a["x"]+aw),self.sy(y),self.sx(b["x"]),self.sy(y),fill="#8A2BE2",dash=(3,3),width=2,arrow=tk.BOTH)
        elif typ == REL_LATER:
            mid=(y1+y2)/2
            self.canvas.create_line(self.sx(x1),self.sy(y1),self.sx(x1),self.sy(mid),self.sx(x2),self.sy(mid),self.sx(x2),self.sy(y2),fill="#8A2BE2",dash=(4,3),width=2,arrow=tk.LAST)
        else:
            mid=(y1+y2)/2
            self.canvas.create_line(self.sx(x1),self.sy(y1),self.sx(x1),self.sy(mid),self.sx(x2),self.sy(mid),self.sx(x2),self.sy(y2),fill="black",width=2,arrow=tk.LAST)

    def legend(self):
        x,y=20,20
        self.canvas.create_rectangle(self.sx(x-10),self.sy(y-10),self.sx(x+210),self.sy(y+210),fill="white",outline="#ccc")
        self.canvas.create_text(self.sx(x),self.sy(y),text="HMC-style",anchor="nw",font=("Arial",11,"bold"))
        items=[("Deposit/Structural","#9FC4E8"),("Surface/Interface","#8AD37D"),("Temporal line","#8A2BE2"),("Phase box","#4B7DBA"),("Period box","#666")]
        for i,(lab,col) in enumerate(items):
            yy=y+28+i*28
            self.canvas.create_rectangle(self.sx(x),self.sy(yy),self.sx(x+22),self.sy(yy+16),fill=col,outline="black")
            self.canvas.create_text(self.sx(x+30),self.sy(yy+8),text=lab,anchor="w",font=("Arial",9))

    def object_hit(self,e):
        x,y=self.canvas.canvasx(e.x),self.canvas.canvasy(e.y)
        for item in reversed(self.canvas.find_overlapping(x,y,x,y)):
            tags=self.canvas.gettags(item)
            if "node" in tags:
                for t in tags:
                    if t in self.nodes: return ("node",t)
            if "gresize" in tags:
                for t in tags:
                    if t.isdigit(): return ("gresize",int(t))
            if "group" in tags:
                for t in tags:
                    if t.isdigit(): return ("group",int(t))
        return (None,None)

    def press(self,e):
        kind,val=self.object_hit(e)
        self.selected=None; self.selected_group=None; self.resize_group=False; self.move_group=False
        x,y=self.ux(self.canvas.canvasx(e.x)),self.uy(self.canvas.canvasy(e.y))
        if kind=="node":
            self.selected=val; n=self.nodes[val]; self.drag=(x-n["x"],y-n["y"])
        elif kind=="gresize":
            self.selected_group=val; self.resize_group=True; g=self.groups[val]; self.drag=(x-(g["x"]+g["w"]),y-(g["y"]+g["h"]))
        elif kind=="group":
            self.selected_group=val; self.move_group=True; g=self.groups[val]; self.drag=(x-g["x"],y-g["y"])
        self.draw()

    def motion(self,e):
        x,y=self.ux(self.canvas.canvasx(e.x)),self.uy(self.canvas.canvasy(e.y))
        dx,dy=self.drag
        if self.selected:
            self.nodes[self.selected]["x"]=round(x-dx); self.nodes[self.selected]["y"]=round(y-dy)
        elif self.selected_group is not None:
            g=self.groups[self.selected_group]
            if self.resize_group:
                g["w"]=max(70,round(x-dx-g["x"])); g["h"]=max(50,round(y-dy-g["y"]))
            elif self.move_group:
                g["x"]=round(x-dx); g["y"]=round(y-dy)
        self.draw()

    def release(self,e): self.resize_group=False; self.move_group=False

    def double(self,e):
        kind,val=self.object_hit(e)
        if kind=="node":
            n=self.nodes[val]
            label=simpledialog.askstring("Name/label","Label:",initialvalue=n.get("label",val),parent=self)
            if label is None: return
            desc=simpledialog.askstring("Description","Description:",initialvalue=n.get("description",""),parent=self)
            typ=simpledialog.askstring("Type","Deposit / Surface / Cut / Fill / Structural / Top / Geology / Unexcavated:",initialvalue=n.get("type","Deposit"),parent=self)
            n["label"], n["description"], n["type"] = label, desc or "", typ or n.get("type","Unknown")
        elif kind=="group":
            g=self.groups[val]
            name=simpledialog.askstring("Group name","Name:",initialvalue=g.get("name",""),parent=self)
            if name is not None: g["name"]=name
        self.draw()

    def update_side_panel(self):
        self.prop.delete("1.0",tk.END)
        if self.selected and self.selected in self.nodes:
            n=self.nodes[self.selected]
            txt=f"id={n.get('id','')}\nlabel={n.get('label','')}\ntype={n.get('type','')}\nname={n.get('name','')}\ndescription={n.get('description','')}\ngroup={n.get('group','')}\nperiod={n.get('period','')}\n"
            self.prop.insert("1.0",txt)
        elif self.selected_group is not None and self.selected_group < len(self.groups):
            g=self.groups[self.selected_group]
            txt=f"id={g.get('id','')}\nname={g.get('name','')}\ntype={g.get('type','Phase')}\ndescription={g.get('description','')}\nmembers={','.join(g.get('members',[]))}\ncollapsed={g.get('collapsed',False)}\n"
            self.prop.insert("1.0",txt)
        self.relations_list.delete(0,tk.END)
        if self.selected:
            for i,e in enumerate(self.edges):
                if e["source"]==self.selected or e["target"]==self.selected:
                    self.relations_list.insert(tk.END, f"{i}: {e['source']} -> {e['target']} [{e.get('type',REL_STRAT)}]")

    def update_props_from_panel(self):
        lines=self.prop.get("1.0",tk.END).splitlines()
        d={}
        for line in lines:
            if "=" in line:
                k,v=line.split("=",1); d[k.strip()]=v.strip()
        if self.selected and self.selected in self.nodes:
            n=self.nodes[self.selected]
            old=n["id"]
            new=d.get("id",old)
            if new != old:
                if new in self.nodes: messagebox.showerror("Fejl","ID findes allerede"); return
                self.nodes[new]=self.nodes.pop(old); n=self.nodes[new]; n["id"]=new
                for e in self.edges:
                    if e["source"]==old: e["source"]=new
                    if e["target"]==old: e["target"]=new
                self.selected=new
            for k in ("label","type","name","description","group","period"):
                if k in d: n[k]=d[k]
        elif self.selected_group is not None and self.selected_group < len(self.groups):
            g=self.groups[self.selected_group]
            for k in ("id","name","type","description"):
                if k in d: g[k]=d[k]
            if "members" in d: g["members"]=[x.strip() for x in d["members"].split(",") if x.strip()]
            if "collapsed" in d: g["collapsed"]=d["collapsed"].lower() in ("true","1","yes","ja")
        self.draw()

    def delete_selected_relation(self):
        sel=self.relations_list.curselection()
        if not sel: return
        text=self.relations_list.get(sel[0])
        idx=int(text.split(":",1)[0])
        if 0 <= idx < len(self.edges):
            del self.edges[idx]
        self.draw()

    def add_node_dialog(self,typ):
        nid=simpledialog.askstring("Ny unit",f"ID for {typ}:",parent=self)
        if not nid: return
        if nid in self.nodes: messagebox.showerror("Fejl","ID findes allerede"); return
        self.nodes[nid]={"id":nid,"label":nid,"type":typ,"x":360,"y":80}
        self.draw()

    def add_edge_dialog(self): self.edge_dialog(REL_STRAT)
    def add_later_dialog(self): self.edge_dialog(REL_LATER)
    def add_contemporary_dialog(self): self.edge_dialog(REL_CONTEMP)

    def edge_dialog(self,typ):
        a=simpledialog.askstring("Relation","Source/yngre:",parent=self)
        b=simpledialog.askstring("Relation","Target/ældre:",parent=self)
        if not a or not b: return
        ok,msg=self.add_edge_checked(a.strip(),b.strip(),typ)
        if not ok: messagebox.showwarning("Relation",msg)
        self.draw()

    def add_edge_checked(self,a,b,typ=REL_STRAT):
        if a==b: return False,"Loop til samme unit er ikke tilladt"
        self.ensure_node(a); self.ensure_node(b)
        # two-unit opposite strat relation: reverse instead of duplicate
        if typ==REL_STRAT and {"source":b,"target":a,"type":REL_STRAT} in self.edges:
            self.edges=[e for e in self.edges if not (e["source"]==b and e["target"]==a and e.get("type")==REL_STRAT)]
        if any(e["source"]==a and e["target"]==b and e.get("type")==typ for e in self.edges):
            return False,"Relation findes allerede"
        if typ in (REL_STRAT,REL_LATER) and self.would_cycle(a,b,typ):
            return False,"Relationen skaber en cyklus"
        self.edges.append({"source":a,"target":b,"type":typ})
        return True,"OK"

    def ensure_node(self,nid):
        if nid not in self.nodes:
            typ="Unknown"
            low=nid.lower()
            if low=="top": typ="Top"
            if low in ("geology","natural"): typ="Geology"
            if low=="unexcavated": typ="Unexcavated"
            self.nodes[nid]={"id":nid,"label":nid,"type":typ,"x":360,"y":80}

    def add_group_dialog(self,gtype):
        name=simpledialog.askstring(gtype,"Name:",parent=self)
        if not name: return
        members=simpledialog.askstring(gtype,"Members separated by comma:",parent=self) or ""
        self.groups.append({"id":name,"name":name,"type":gtype,"members":[m.strip() for m in members.split(",") if m.strip()],"x":300,"y":260,"w":360,"h":190,"collapsed":False})
        self.auto_fit_groups()

    def toggle_group(self):
        if self.selected_group is not None:
            g=self.groups[self.selected_group]; g["collapsed"]=not g.get("collapsed",False); self.draw()
        else:
            messagebox.showinfo("Collapse","Vælg en phase/period-boks først")

    def graph_edges_for_validation(self, include_temporal=True):
        out=[]
        for e in self.edges:
            typ=e.get("type",REL_STRAT)
            if typ==REL_CONTEMP: continue
            if typ==REL_LATER and not include_temporal: continue
            out.append((e["source"],e["target"]))
        return out

    def would_cycle(self,a,b,typ):
        edges=self.graph_edges_for_validation(include_temporal=True)+[(a,b)]
        g=defaultdict(list)
        for s,t in edges: g[s].append(t)
        stack=[b]; seen=set()
        while stack:
            n=stack.pop()
            if n==a: return True
            if n in seen: continue
            seen.add(n); stack += g.get(n,[])
        return False

    def transitive_reduction(self):
        # remove redundant stratigraphic/later lines; contemporary retained
        base=[e for e in self.edges if e.get("type") in (REL_STRAT,REL_LATER)]
        keep=[e for e in self.edges if e.get("type")==REL_CONTEMP]
        g=defaultdict(list)
        for e in base: g[e["source"]].append(e["target"])
        for e in base:
            a,b=e["source"],e["target"]
            found=False
            for mid in g[a]:
                if mid==b: continue
                stack=[mid]; seen=set()
                while stack:
                    x=stack.pop()
                    if x==b: found=True; break
                    if x in seen: continue
                    seen.add(x); stack += g.get(x,[])
                if found: break
            if not found: keep.append(e)
        self.edges=keep

    def validate(self):
        problems=[]; warnings=[]
        # validity: every normal unit except Top and Geology should have above and below
        incoming=defaultdict(int); outgoing=defaultdict(int)
        for e in self.edges:
            if e.get("type") in (REL_STRAT,REL_LATER):
                outgoing[e["source"]]+=1; incoming[e["target"]]+=1
        for nid,n in self.nodes.items():
            typ=n.get("type","Unknown")
            if typ not in ("Top","Geology"):
                if incoming[nid]==0 and typ!="Top": warnings.append(f"{nid}: mangler relation ovenfra/yngre")
                if outgoing[nid]==0 and typ!="Geology": warnings.append(f"{nid}: mangler relation nedad/ældre")
            if typ=="Unknown": warnings.append(f"{nid}: type er Unknown")
        # top/geology constraints
        for e in self.edges:
            if e["target"]=="Top": problems.append("Intet må ligge over Top surface")
            if e["source"]=="Geology": problems.append("Geology/interface må ikke ligge over andre units")
        # cycles
        g=defaultdict(list)
        for s,t in self.graph_edges_for_validation(True): g[s].append(t)
        temp=set(); perm=set()
        def visit(n,path):
            if n in temp: problems.append("Cyklus: "+" -> ".join(path+[n])); return
            if n in perm: return
            temp.add(n)
            for m in g.get(n,[]): visit(m,path+[n])
            temp.remove(n); perm.add(n)
        for n in self.nodes: visit(n,[])
        # contemporary same layer warning after layout check
        for e in self.edges:
            if e.get("type")==REL_CONTEMP and e["source"] in self.nodes and e["target"] in self.nodes:
                if abs(self.nodes[e["source"]]["y"]-self.nodes[e["target"]]["y"]) > 10:
                    warnings.append(f"{e['source']} contemporary {e['target']} men ligger ikke på samme niveau")
        return problems,warnings

    def validate_show(self):
        p,w=self.validate()
        for n in self.nodes.values(): n["invalid"]=False
        for msg in p+w:
            for nid in self.nodes:
                if nid in msg: self.nodes[nid]["invalid"]=True
        self.draw()
        if not p and not w: messagebox.showinfo("Validity","✓ Valid matrix")
        else:
            txt=""
            if p: txt+="FEJL:\n"+"\n".join("• "+x for x in p)+"\n\n"
            if w: txt+="ADVARSLER:\n"+"\n".join("• "+x for x in w)
            (messagebox.showerror if p else messagebox.showwarning)("Validity check",txt)

    def auto_layout(self):
        p,w=self.validate()
        if p:
            messagebox.showerror("Auto-layout","Matrixen har fejl/cyklusser. Ret dem før auto-layout.")
            return
        self.transitive_reduction()
        edges=self.graph_edges_for_validation(include_temporal=self.show_temporal.get())
        children=defaultdict(list); indeg={n:0 for n in self.nodes}
        for a,b in edges:
            children[a].append(b); indeg[b]=indeg.get(b,0)+1; indeg.setdefault(a,0)
        level={n:0 for n in self.nodes}
        q=deque([n for n,d in indeg.items() if d==0])
        while q:
            n=q.popleft()
            for m in children.get(n,[]):
                level[m]=max(level.get(m,0), level[n]+1)
                indeg[m]-=1
                if indeg[m]==0: q.append(m)
        # contemporary: force same layer by max/min compromise
        for e in self.edges:
            if e.get("type")==REL_CONTEMP:
                a,b=e["source"],e["target"]
                lv=max(level.get(a,0),level.get(b,0))
                level[a]=level[b]=lv
        maxlev=max(level.values()) if level else 0
        for nid,n in self.nodes.items():
            typ=n.get("type")
            if typ=="Top": level[nid]=0
            if typ in ("Geology","Natural"): level[nid]=maxlev+1
            if typ=="Unexcavated": level[nid]=maxlev
        buckets=defaultdict(list)
        for nid in self.nodes: buckets[level.get(nid,0)].append(nid)
        def key(nid):
            n=self.nodes[nid]
            return (n.get("period",""), n.get("group",""), self.primary_num(nid), nid)
        for lev in sorted(buckets):
            arr=sorted(buckets[lev], key=key)
            for i,nid in enumerate(arr):
                self.nodes[nid]["x"]=300+i*155
                self.nodes[nid]["y"]=70+lev*100
        self.auto_fit_groups(draw=False)
        self.draw()
        self.status.set("Auto-layout applied: stratigraphic/later = vertical; contemporary = horizontal")

    def primary_num(self,s):
        m=re.search(r'\d+',s); return int(m.group()) if m else 999999

    def auto_fit_groups(self, draw=True):
        for g in self.groups:
            if g.get("collapsed"): continue
            members=[self.nodes[m] for m in g.get("members",[]) if m in self.nodes]
            if not members:
                name=g.get("name","")
                members=[n for n in self.nodes.values() if n.get("group")==name or n.get("period")==name]
            if members:
                minx=min(n["x"] for n in members)-45
                miny=min(n["y"] for n in members)-55
                maxx=max(n["x"]+n.get("w",BOX_W) for n in members)+45
                maxy=max(n["y"]+n.get("h",BOX_H) for n in members)+45
                g.update({"x":minx,"y":miny,"w":maxx-minx,"h":maxy-miny})
        if draw: self.draw()

    def import_rel_text(self):
        p=filedialog.askopenfilename(filetypes=[("Text","*.txt"),("All files","*.*")])
        if not p: return
        text=Path(p).read_text(encoding="utf-8",errors="ignore")
        added=0
        patterns=[
            (r'\b(\w+)\s+(?:above|over|overlejrer|ligger over)\s+(\w+)\b', REL_STRAT, False),
            (r'\b(\w+)\s+(?:below|under|ligger under)\s+(\w+)\b', REL_STRAT, True),
            (r'\b(\w+)\s+(?:later than|senere end)\s+(\w+)\b', REL_LATER, False),
            (r'\b(\w+)\s+(?:contemporary with|samtidig med)\s+(\w+)\b', REL_CONTEMP, False),
        ]
        for line in text.splitlines():
            for pat,typ,reverse in patterns:
                for m in re.finditer(pat,line,re.I):
                    a,b=m.group(1),m.group(2)
                    if reverse: a,b=b,a
                    ok,_=self.add_edge_checked(a,b,typ)
                    if ok: added+=1
        self.auto_layout()
        messagebox.showinfo("Import tekst",f"Importerede {added} relationer")

    def import_hmcx(self):
        p=filedialog.askopenfilename(filetypes=[("HMCX","*.hmcx"),("XML","*.xml"),("All files","*.*")])
        if not p: return
        text=Path(p).read_text(encoding="utf-8",errors="ignore")
        added_n=0; added_e=0
        try:
            root=ET.fromstring(text)
            for el in root.iter():
                attrs={k.lower():v for k,v in el.attrib.items()}
                tag=el.tag.lower()
                # generic node import
                nid=attrs.get("id") or attrs.get("unitid") or attrs.get("context") or attrs.get("label") or attrs.get("name")
                if nid and (tag.endswith("unit") or tag.endswith("node") or re.match(r'^(F?\d+|Top|Geology|Unexcavated)$',nid,re.I)):
                    if nid not in self.nodes:
                        typ=attrs.get("type","Unknown")
                        self.nodes[nid]={"id":nid,"label":attrs.get("label",nid),"name":attrs.get("name",""),"description":attrs.get("description",""),"type":typ,"x":300,"y":80}
                        added_n+=1
                # relation import
                s=attrs.get("source") or attrs.get("from") or attrs.get("above") or attrs.get("younger")
                t=attrs.get("target") or attrs.get("to") or attrs.get("below") or attrs.get("older")
                typ=attrs.get("relation") or attrs.get("type") or REL_STRAT
                rel=REL_STRAT
                if "later" in typ.lower(): rel=REL_LATER
                if "contemp" in typ.lower(): rel=REL_CONTEMP
                if s and t:
                    ok,_=self.add_edge_checked(s,t,rel)
                    if ok: added_e+=1
        except Exception:
            # fallback line parsing
            for a,b in re.findall(r'(F\d+)[^\n\r]{0,80}(?:above|source|from)[^\n\r]{0,80}(F\d+)',text,re.I):
                ok,_=self.add_edge_checked(a,b,REL_STRAT)
                if ok: added_e+=1
        self.auto_layout()
        messagebox.showinfo("Import HMCX",f"Importerede ca. {added_n} units og {added_e} relationer.\nKontrollér resultatet, da HMCX kan variere.")

    def export_hmcx(self):
        p=filedialog.asksaveasfilename(defaultextension=".hmcx",filetypes=[("HMCX","*.hmcx")])
        if not p: return
        root=ET.Element("hmcx")
        units=ET.SubElement(root,"units")
        for n in self.nodes.values():
            ET.SubElement(units,"unit",id=n["id"],label=n.get("label",n["id"]),type=n.get("type","Unknown"),name=n.get("name",""),description=n.get("description",""),x=str(n.get("x",0)),y=str(n.get("y",0)))
        rels=ET.SubElement(root,"relations")
        for e in self.edges:
            ET.SubElement(rels,"relation",source=e["source"],target=e["target"],type=e.get("type",REL_STRAT))
        groups=ET.SubElement(root,"groups")
        for g in self.groups:
            ge=ET.SubElement(groups,"group",id=g.get("id",g.get("name","")),name=g.get("name",""),type=g.get("type","Phase"),collapsed=str(g.get("collapsed",False)),x=str(g.get("x",0)),y=str(g.get("y",0)),w=str(g.get("w",100)),h=str(g.get("h",100)))
            for m in g.get("members",[]): ET.SubElement(ge,"member",id=m)
        ET.ElementTree(root).write(p,encoding="utf-8",xml_declaration=True)
        messagebox.showinfo("Eksport HMCX",p)

    def export_svg(self):
        p=filedialog.asksaveasfilename(defaultextension=".svg",filetypes=[("SVG","*.svg")])
        if not p: return
        Path(p).write_text(self.to_svg(),encoding="utf-8")
        messagebox.showinfo("SVG",p)

    def export_pdf(self):
        p=filedialog.asksaveasfilename(defaultextension=".pdf",filetypes=[("PDF","*.pdf")])
        if not p: return
        try:
            from reportlab.pdfgen import canvas
            from reportlab.lib.pagesizes import A3, landscape
            from reportlab.lib.colors import HexColor, black
            c=canvas.Canvas(p,pagesize=landscape(A3)); page_w,page_h=landscape(A3)
            xs=[]; ys=[]
            for n in self.nodes.values():
                xs += [n["x"], n["x"]+n.get("w",BOX_W)]; ys += [n["y"], n["y"]+n.get("h",BOX_H)]
            for g in self.groups:
                xs += [g["x"],g["x"]+g.get("w",100)]; ys += [g["y"],g["y"]+g.get("h",100)]
            if not xs: xs=[0,100]; ys=[0,100]
            minx,miny,maxx,maxy=min(xs)-80,min(ys)-80,max(xs)+80,max(ys)+80
            scale=min((page_w-60)/(maxx-minx),(page_h-60)/(maxy-miny))
            def tx(x): return 30+(x-minx)*scale
            def ty(y): return page_h-(30+(y-miny)*scale)
            c.setTitle("Harris Matrix")
            c.setDash(6,4)
            for g in self.groups:
                c.setStrokeColor(HexColor("#4B7DBA") if g.get("type")=="Phase" else HexColor("#666666"))
                c.rect(tx(g["x"]),ty(g["y"]+g["h"]),g["w"]*scale,g["h"]*scale,fill=0,stroke=1)
                c.drawString(tx(g["x"]+8),ty(g["y"]+16),f"{g.get('type','Group')}: {g.get('name','')}")
            c.setDash(); c.setStrokeColor(black)
            for e in self.edges:
                if e["source"] in self.nodes and e["target"] in self.nodes:
                    a,b=self.nodes[e["source"]],self.nodes[e["target"]]
                    aw,ah=a.get("w",BOX_W),a.get("h",BOX_H); bw,bh=b.get("w",BOX_W),b.get("h",BOX_H)
                    x1,y1=a["x"]+aw/2,a["y"]+ah; x2,y2=b["x"]+bw/2,b["y"]; mid=(y1+y2)/2
                    if e.get("type")!=REL_STRAT: c.setDash(3,3)
                    else: c.setDash()
                    for (xa,ya),(xb,yb) in zip([(x1,y1),(x1,mid),(x2,mid)],[(x1,mid),(x2,mid),(x2,y2)]):
                        c.line(tx(xa),ty(ya),tx(xb),ty(yb))
            c.setDash()
            for n in self.nodes.values():
                x,y,w,h=n["x"],n["y"],n.get("w",BOX_W),n.get("h",BOX_H)
                c.setFillColor(HexColor(TYPE_COLORS.get(n.get("type","Unknown"),"#EEEEEE")))
                c.rect(tx(x),ty(y+h),w*scale,h*scale,fill=1,stroke=1)
                c.setFillColor(black); c.drawCentredString(tx(x+w/2),ty(y+h/2)+3,n.get("label",n["id"]).replace("\n"," ")[:30])
            c.save(); messagebox.showinfo("PDF",p)
        except Exception as e:
            messagebox.showerror("PDF fejl",str(e))

    def to_svg(self):
        parts=['<svg xmlns="http://www.w3.org/2000/svg" width="3200" height="2400" viewBox="0 0 3200 2400"><rect width="100%" height="100%" fill="white"/>']
        for g in self.groups:
            col="#4B7DBA" if g.get("type")=="Phase" else "#666"
            parts.append(f'<rect x="{g["x"]}" y="{g["y"]}" width="{g["w"]}" height="{g["h"]}" fill="none" stroke="{col}" stroke-width="2" stroke-dasharray="6 4"/>')
            parts.append(f'<text x="{g["x"]+8}" y="{g["y"]+18}" font-family="Arial" font-size="14" font-weight="bold" fill="{col}">{esc(g.get("type","Group"))}: {esc(g.get("name",""))}</text>')
        for e in self.edges:
            if e["source"] in self.nodes and e["target"] in self.nodes:
                a,b=self.nodes[e["source"]],self.nodes[e["target"]]
                aw,ah=a.get("w",BOX_W),a.get("h",BOX_H); bw,bh=b.get("w",BOX_W),b.get("h",BOX_H)
                x1,y1=a["x"]+aw/2,a["y"]+ah; x2,y2=b["x"]+bw/2,b["y"]; mid=(y1+y2)/2
                col="#8A2BE2" if e.get("type")!=REL_STRAT else "black"
                dash=' stroke-dasharray="4 3"' if e.get("type")!=REL_STRAT else ""
                parts.append(f'<polyline points="{x1},{y1} {x1},{mid} {x2},{mid} {x2},{y2}" fill="none" stroke="{col}" stroke-width="2"{dash}/>')
        for n in self.nodes.values():
            x,y,w,h=n["x"],n["y"],n.get("w",BOX_W),n.get("h",BOX_H)
            c=TYPE_COLORS.get(n.get("type","Unknown"),"#EFEFEF")
            parts.append(f'<rect x="{x}" y="{y}" width="{w}" height="{h}" fill="{c}" stroke="black" stroke-width="1.5"/>')
            lines=n.get("label",n["id"]).split("\\n")
            for j,line in enumerate(lines):
                yy=y+h/2+(j-(len(lines)-1)/2)*13+4
                parts.append(f'<text x="{x+w/2}" y="{yy}" text-anchor="middle" font-family="Arial" font-size="12" font-weight="bold">{esc(line)}</text>')
        parts.append("</svg>"); return "\n".join(parts)

    def search_dialog(self):
        q=simpledialog.askstring("Search","Search id/name/description:",parent=self)
        if not q: return
        self.search_list.delete(0,tk.END)
        q=q.lower()
        for nid,n in self.nodes.items():
            hay=" ".join(str(n.get(k,"")) for k in ("id","label","name","description","type")).lower()
            if q in hay: self.search_list.insert(tk.END,nid)

    def goto_search_result(self,e=None):
        sel=self.search_list.curselection()
        if not sel: return
        nid=self.search_list.get(sel[0])
        if nid in self.nodes:
            n=self.nodes[nid]; self.selected=nid
            self.canvas.xview_moveto(max(0,self.sx(n["x"]-300)/3200))
            self.canvas.yview_moveto(max(0,self.sy(n["y"]-250)/2400))
            self.draw()

    def add_bookmark(self):
        name=simpledialog.askstring("Bookmark","Name:",parent=self)
        if not name: return
        self.bookmarks.append({"name":name,"x":self.canvas.canvasx(0)/self.zoom,"y":self.canvas.canvasy(0)/self.zoom})
        self.search_list.insert(tk.END,"BM: "+name)

    def goto_bookmark(self):
        if not self.bookmarks: messagebox.showinfo("Bookmark","Ingen bookmarks"); return
        names=[b["name"] for b in self.bookmarks]
        name=simpledialog.askstring("Go bookmark","Name:\n"+", ".join(names),parent=self)
        for b in self.bookmarks:
            if b["name"]==name:
                self.canvas.xview_moveto(max(0,self.sx(b["x"])/3200)); self.canvas.yview_moveto(max(0,self.sy(b["y"])/2400)); return

    def set_zoom(self,z):
        self.zoom=max(0.25,min(3.0,z)); self.draw()
    def fit_view(self):
        self.zoom=0.75; self.canvas.xview_moveto(0); self.canvas.yview_moveto(0); self.draw()
    def on_mousewheel(self,e):
        self.set_zoom(self.zoom*(1.08 if e.delta>0 else 1/1.08))

    def open_json(self):
        p=filedialog.askopenfilename(filetypes=[("JSON","*.json")])
        if p: self.filename=p; self.load_json(json.load(open(p,encoding="utf-8")))
    def load_json(self,d):
        self.nodes={n["id"]:dict(n) for n in d.get("nodes",[])}
        self.edges=[dict(e) for e in d.get("edges",[])]
        self.groups=list(d.get("groups",[])); self.bookmarks=list(d.get("bookmarks",[]))
        self.draw()
    def save_json(self):
        if not self.filename: return self.save_json_as()
        d={"nodes":list(self.nodes.values()),"edges":self.edges,"groups":self.groups,"bookmarks":self.bookmarks}
        json.dump(d,open(self.filename,"w",encoding="utf-8"),ensure_ascii=False,indent=2); messagebox.showinfo("Gemt",self.filename)
    def save_json_as(self):
        p=filedialog.asksaveasfilename(defaultextension=".json",filetypes=[("JSON","*.json")])
        if p: self.filename=p; self.save_json()

if __name__=="__main__":
    HarrisApp().mainloop()
