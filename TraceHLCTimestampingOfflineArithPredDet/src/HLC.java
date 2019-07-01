import java.util.Vector;
class HLC extends Clock
{
    Vector<Integer> hlc;
    //int l;
    //int c;
    //int pt;
    //HLC(int nwpt, int nwl, int nwc)
    HLC(Vector<Integer> newTime)
    {
        //super(newTime);
        hlc=new Vector<Integer>();
        hlc.add(newTime.get(0));
        hlc.add(newTime.get(1));
        hlc.add(newTime.get(2));
    }
    int getPt()
    {
        return hlc.get(0);
    }
    int getL()
    {
        return hlc.get(1);
    }
    int getC()
    {
        return hlc.get(2);
    }
    void setPt(int physicalTime)
    {
        hlc.set(0,physicalTime);
    }
    void setL(int nwL)
    {
        hlc.set(1,nwL);
    }
    void setC(int nwC)
    {
        hlc.set(2,nwC);
    }
    void setClock(Vector<Integer> newTime)
    {
        hlc.set(0,newTime.get(0));
        hlc.set(1,newTime.get(1));
        hlc.set(2,newTime.get(2));
    }
    Vector<Integer> getClock()
    {
        return hlc;
    }

    boolean lessThan(Clock hlctocomparewith)
    {
        Vector<Integer> otherclk =hlctocomparewith.getClock();
        int other_l=otherclk.get(1);
        int other_c=otherclk.get(2);
        if((getL()<other_l)||((getL()==other_l)&&(getC()<other_c)))
        {
            return true;
        }
        else
        {
            return false;
        }
    }
    boolean equalTo(Clock hlctocomparewith)
    {
        Vector<Integer> otherclk =hlctocomparewith.getClock();
        int other_l=otherclk.get(1);
        int other_c=otherclk.get(2);
        if((getL()==other_l)&&(getC()==other_c))
        {
            return true;
        }
        else
        {
            return false;
        }
    }
    void updateLocal(int physicalTime)
    {
        if (getPt()==physicalTime)//typically gets executed only msg send cases
        {
            //update only c
            int updatedcvalue=getC()+1;
            setC(updatedcvalue);
            setL(getL());
        }
        else
        {
            if(getL()>=physicalTime)//typically gets executed only msg send cases-- because for msg recieve it is handled in "characters(..)" function
            {
                int updatedcvalue=getC()+1;
                setC(updatedcvalue);
                setL(getL());

                //if(pt<physicalTime)
                if(getPt()<physicalTime)
                {
                    //pt=physicalTime;
                    setPt(physicalTime);
                }
            }
            else//can get executed during msg send/receive
            {
                //update l
                //l=physicalTime;
                setL(physicalTime);
                //c=0;
                setC(0);
                //pt=physicalTime;
                setPt(physicalTime);
            }
        }
    }
    void updateMsgRcv(int receiver_time, Clock sndrClk)
    {
        //l.j := max(l0.j, l.m, pt.j)
        int maxofall=Math.max(Math.max(sndrClk.getClock().get(1),receiver_time),getL());

        //HLC update l,c on msg receive
        if(maxofall==getL())
        {
            setL(getL());//proc.setL(proc.getL());
            setC(getC()+1);//proc.setC(proc.getC()+1);
            setPt(receiver_time);//proc.setPt(receiver_time);
        }
        else if(maxofall==receiver_time)
        {
            //System.out.println("CLOCK UPDATED");//
            updateLocal(receiver_time);
        }
        else//Elseif (l.j=l.m) then c.j := c.m + 1//hlc code
        {
            setL(sndrClk.getClock().get(1));
            setC(sndrClk.getClock().get(2)+1);
            setPt(receiver_time);
        }
    }
    void setClockPlusValue(int inc) {
        this.hlc.set(1, this.hlc.get(1)+inc);
    }
    void setClockMinusValue(int inc) {
        if (this.hlc.get(1)>= inc) {
            this.hlc.set(1, this.hlc.get(1)-inc);
        }
        else {
            this.hlc.set(1,0);
        }
    }
}