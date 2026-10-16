"""Vector drawing primitives; copied into each independent project generator."""
import argparse
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle, Polygon, Circle, FancyArrowPatch

plt.rcParams.update({'font.family':'STIXGeneral', 'mathtext.fontset':'stix',
                     'font.size':9, 'pdf.fonttype':42, 'ps.fonttype':42,
                     'text.usetex':False, 'axes.unicode_minus':False})
CM = 1 / 2.54

class Drawing:
    def __init__(self, bounds):
        x0,y0,x1,y1 = bounds
        self.fig = plt.figure(figsize=((x1-x0)*CM,(y1-y0)*CM))
        self.ax = self.fig.add_axes([0,0,1,1], xlim=(x0,x1), ylim=(y0,y1))
        self.ax.set_aspect('equal'); self.ax.axis('off')
        self.nodes = {}
        self.labels = []

    def text(self,x,y,label,size=9,ha='center',va='center'):
        artist=self.ax.text(x,y,label,fontsize=size,ha=ha,va=va,
                            linespacing=1.15,clip_on=False,zorder=4)
        self.labels.append([artist,None])
        return artist

    def box(self,name,x,y,w,h,label,dashed=False,shape='rect',size=9):
        style = {'edgecolor':'black','facecolor':'white','linewidth':.55,
                 'linestyle':(0,(4,3)) if dashed else 'solid', 'zorder':2}
        if shape == 'diamond':
            obj = Polygon([(x-w/2,y),(x,y+h/2),(x+w/2,y),(x,y-h/2)],**style)
        elif shape == 'circle': obj = Circle((x,y),w/2,**style)
        else: obj = Rectangle((x-w/2,y-h/2),w,h,**style)
        self.ax.add_patch(obj); self.text(x,y,label,size)
        self.labels[-1][1]=(x-w/2,y-h/2,x+w/2,y+h/2)
        self.nodes[name] = (x,y,w,h,shape)

    def point(self,name,side):
        x,y,w,h,_ = self.nodes[name]
        return {'n':(x,y+h/2),'s':(x,y-h/2),'e':(x+w/2,y),
                'w':(x-w/2,y),'nw':(x-w/2,y+h/2),
                'ne':(x+w/2,y+h/2),'c':(x,y)}[side]

    def line(self,points,dashed=False):
        xs,ys=zip(*points)
        self.ax.plot(xs,ys,color='black',linewidth=.55,
                     linestyle=(0,(4,3)) if dashed else 'solid',zorder=1)

    def arrow(self,p,q,dashed=False,via=()):
        points=[p,*via,q]
        if via:self.line(points[:-1],dashed)
        self.ax.add_patch(FancyArrowPatch(points[-2],points[-1],
                         arrowstyle='-|>',mutation_scale=7.5,linewidth=.55,
                         color='black',shrinkA=0,shrinkB=0,
                         linestyle=(0,(4,3)) if dashed else 'solid',zorder=1))

    def edge(self,a,b,sa='s',sb='n',**kwargs):
        self.arrow(self.point(a,sa),self.point(b,sb),**kwargs)

    def frame(self,x,y,w,h):
        self.ax.add_patch(Rectangle((x,y),w,h,fill=False,edgecolor='black',
                                   linewidth=.55,linestyle=(0,(4,3)),zorder=0))

    def save(self,out,name):
        # Fixed physical canvas: do not enlarge or rasterize the scientific figure.
        self.fig.canvas.draw()
        renderer=self.fig.canvas.get_renderer()
        x0,x1=self.ax.get_xlim();y0,y1=self.ax.get_ylim()
        for artist,node in self.labels:
            b=artist.get_window_extent(renderer).transformed(self.ax.transData.inverted())
            if b.x0<x0-.02 or b.x1>x1+.02 or b.y0<y0-.02 or b.y1>y1+.02:
                raise ValueError(name+': clipped label '+repr(artist.get_text()))
            if node and (b.x0<node[0]-.02 or b.x1>node[2]+.02 or b.y0<node[1]-.02 or b.y1>node[3]+.02):
                raise ValueError(name+': label exceeds node '+repr(artist.get_text()))
        self.fig.savefig(out/(name+'.pdf'),format='pdf',
                         metadata={'Creator':'Python Matplotlib','Producer':None,
                                   'CreationDate':None,'ModDate':None})
        plt.close(self.fig)


def survival(out):
    d=Drawing((-1,-.7,7.5,6.05))
    for name,x,label,dead in [('req',0,'$r$\nreq',False),('ra',2.1,r'$\neg r\vee a$'+'\nrule-a',True),('rb',4.2,r'$\neg r\vee a$'+'\nrule-b',False),('bad',6.3,r'$\neg a$'+'\nbad',False)]:
        d.box(name,x,.35,1.6,.8,label,dashed=dead,size=8)
    d.box('or',3.15,1.5,.5,.5,r'$\vee$',shape='circle',size=8)
    d.box('body',3.15,2.2,1.6,.55,r'$\neg r\vee a$',size=8)
    d.edge('ra','or','n','w',dashed=True);d.edge('rb','or','n','e')
    # Inference edges rise from premises to the checked resolution node.
    d.arrow(d.point('or','n'),d.point('body','s'))
    d.box('and1',4.7,3.05,.5,.5,r'$\wedge$',shape='circle',size=8)
    d.box('notr',4.7,3.8,1.4,.55,r'$\neg r$',size=8)
    d.edge('body','and1','n','w');d.text(3.4,2.8,'$a$',8)
    d.edge('bad','and1','n','e',via=((6.3,3.05),))
    d.arrow(d.point('and1','n'),d.point('notr','s'))
    d.box('and2',2.1,4.55,.5,.5,r'$\wedge$',shape='circle',size=8)
    d.box('empty',2.1,5.25,1.4,.55,'\u25a1',size=8)
    d.edge('notr','and2','n','e');d.text(3.5,4.45,'$r$',8)
    d.edge('req','and2','n','w',via=((0,4.55),))
    d.arrow(d.point('and2','n'),d.point('empty','s'))
    d.text(5.35,5.55,'Checked resolution\nschemas',8)
    d.text(3.15,-.35,'Exact version leaves; dashed: deleted in target',8)
    d.save(out,'survival-circuit')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parent)
    a=parser.parse_args();a.output.mkdir(parents=True,exist_ok=True);survival(a.output)

