import java.io.FileWriter;
import java.io.IOException;
import java.io.BufferedWriter;
import java.io.File;
import java.util.Vector;
import java.util.Deque;
import java.util.ArrayDeque;
class Process
{
    int id;
    int prev_pt;
    int lastsendorrecorlocevntpt;//variable to check if multiple events -msg send/rcv or local event happened at the same instant --used to update prev(Old) pt,l,c only when the first event occurs at a specific physical time

    Clock clock=new Clock();
    Clock prev_clock=new Clock();
    //queue to remember interval-candidates
    Deque<Candidate> candQueue;
    //queue to remember values corresponding to message sends
    Deque<MessageSendStruct> log;
    int msg_counter;

    Deque<ChangePoint> cPointQueue;

    Process(int unique_id, Clock nwclock)
    {
        id=unique_id;
        clock=nwclock;

        msg_counter=0;
        if(TraceHLCTimestampingOfflineArithPredDet.clockmode.equals("HLC"))
        {
            Vector<Integer> hlcvector=new Vector<Integer>();
            hlcvector.add(0);
            hlcvector.add(0);
            hlcvector.add(0);
            prev_clock= new HLC(hlcvector);
        }
        prev_pt=0;
        log = new ArrayDeque<MessageSendStruct>();
        candQueue= new ArrayDeque<Candidate>();
        cPointQueue= new ArrayDeque<ChangePoint>();
        lastsendorrecorlocevntpt=-1;
    }

    void setId(int passed_id){id=passed_id;}
    void setProcClock(Clock nwclock){clock.setClock(nwclock.getClock());}
    void setProcOldClock(Clock passed_clock){prev_clock.setClock(passed_clock.getClock());}
    void setlastsendorrecorlocevntpt(int sendreclocventpt){lastsendorrecorlocevntpt=sendreclocventpt;}

    int getId(){return id;}
    Clock getProcClock(){return clock;}
    Clock getProcOldClock(){return prev_clock;}

    int getlastsendorrecorlocevntpt(){return lastsendorrecorlocevntpt;}

    Deque<Candidate> getCandQueue()
    {
        return candQueue;
    }

    void setCandQueue(Deque<Candidate> updatedQueue)
    {
        candQueue=updatedQueue;
    }
    Deque<ChangePoint> getCPtQueue()
    {
        return cPointQueue;
    }

    void setCPtQueue(Deque<ChangePoint> updatedQueue)
    {
        cPointQueue=updatedQueue;
    }

    //clear queue method at a process - given time x --CLEARQUEUE
    Candidate clearQueueTill(Clock tillend)
    {
        //System.out.println("clear queue at process"+id+"tillendl"+tillendl+"tillendc"+tillendc);
        while(!(candQueue.isEmpty()) &&(((candQueue.peekFirst()).getEndClock().lessThan(tillend)) || ((candQueue.peekFirst()).getEndClock().equalTo(tillend))))
        {
            //pop all candidates with start time smaller than x
            candQueue.removeFirst();
        }
        //set the front candidate in my queue as my representative in Token--will be done at the method that called this method
        return candQueue.peekFirst();
    }

    Candidate newCandidateOccurance(Clock intervalstart, Clock intervalend)
    {
        Candidate newCand= new Candidate(intervalstart, intervalend);
        candQueue.add(newCand);
        if(TraceHLCTimestampingOfflineArithPredDet.debugmode==2)
        {
            //JUST FOR DEBUGGING
            try
            {
                //System.out.println("Pushing Candidate");
                BufferedWriter candbw2= new BufferedWriter(new FileWriter("Candidates"+id+".txt", true));//true for append
                candbw2.append("<"+intervalstart.getClock()+"> to <"+intervalend.getClock()+">\n");
                candbw2.close();
            }
            catch (Exception e)
            {
                e.printStackTrace();
            }
        }
        return newCand;
    }
    void newChangePoint(Clock cPtTime, int endPtIdentifier)
    {
        ChangePoint newCPt= new ChangePoint(cPtTime, endPtIdentifier);
        cPointQueue.add(newCPt);
        if(TraceHLCTimestampingOfflineArithPredDet.debugmode==2)
        {
            //JUST FOR DEBUGGING
            try
            {
                //System.out.println("Pushing Candidate");
                BufferedWriter cptbw2= new BufferedWriter(new FileWriter("ChangePoints"+id+".txt", true));//true for append
                cptbw2.append("<"+cPtTime.getClock()+", type: "+endPtIdentifier+">\n");
                cptbw2.close();
            }
            catch (Exception e)
            {
                e.printStackTrace();
            }
        }
    }
    void updateClockLocalOrSengMsg(int physicalTime, boolean sendmsg)
    {
        if(lastsendorrecorlocevntpt!=physicalTime)//if a message send/receive did not happen at the same instant update old pt - otherwise don't because old pt is required for interval reporting
        {//pt is also same-still update old_value
            setProcOldClock(getProcClock());
        }
        clock.updateLocal(physicalTime);

        //System.out.println("At Process:"+id+"; Physical Time:"+physicalTime);

        if(sendmsg)
        {
            Clock formsgclk=new Clock();
            //push message id, l, c into queue
            if(TraceHLCTimestampingOfflineArithPredDet.clockmode.equals("HLC"))
            {
                Vector<Integer> hlcvector=new Vector<Integer>();
                hlcvector.add(0);
                hlcvector.add(0);
                hlcvector.add(0);
                formsgclk=new HLC(hlcvector);
            }
            formsgclk.setClock(clock.getClock());//copying clock values to new clk object for msg timestamping
            MessageSendStruct newmsg= new MessageSendStruct(msg_counter++,formsgclk);
            log.add(newmsg);
        }

        setlastsendorrecorlocevntpt(physicalTime);
    }
    void updateClockMessageRceive(int receiver_time, Clock sndrClk)
    {
        if(getlastsendorrecorlocevntpt()!=receiver_time)
        {
            setProcOldClock(getProcClock());

        }
        clock.updateMsgRcv(receiver_time,sndrClk);

        setlastsendorrecorlocevntpt(receiver_time);
    }
    MessageSendStruct getClockfromQueue(int passed_phytime)
    {
        while(log.peek().getMsgClock().getClock().get(0)!=passed_phytime)
        {
            //System.out.println(passed_phytime+","+log.peek().getPt());
            System.out.println("FIFO VIOLATED...popping..");
            log.removeFirst();
        }
        MessageSendStruct msgptclk=log.peek();
        if(msgptclk!=null)
        {
            if(passed_phytime == msgptclk.getMsgClock().getClock().get(0))
            {
                //System.out.println("FOUND MATCHING SEND");
                return log.removeFirst();
            }
            else
            {
                System.out.println("CODE THAT SHOULD NOT EXECUTE");
                System.exit(0);
            }
            return log.peek();
        }
        else
        {
            System.out.println("SEND QUEUE EMPTY");
            System.exit(0);
            return msgptclk;
        }
    }

    void printCandQueueToFile(String inpfilename) {
        //********************************create needed file, then print candidates*******************************
        BufferedWriter bw_deb1=null;
        try
        {
            File ifilename = new File(inpfilename);
            if(!ifilename.exists()) //if file does not exist already
            {
                ifilename.getParentFile().mkdirs(); //create all necessary parent directories
                bw_deb1= new BufferedWriter(new FileWriter(ifilename));//opening file in write mode so anything already existing will be cleared
            }
            else
            {
                bw_deb1= new BufferedWriter(new FileWriter(ifilename,true));//opening file in write mode so anything already existing will be cleared
            }

            if (!candQueue.isEmpty())//if there is at least one unprocessed changepoint
            {
                bw_deb1.write("Process "+id);
                bw_deb1.newLine();
                //print all the elements available in deque
                for (Candidate cand : candQueue)
                {
                    bw_deb1.write("<"+cand.getStartClock().getClock().get(1)+","+cand.getStartClock().getClock().get(2)+">-<" + cand.getEndClock().getClock().get(1)+","+ cand.getEndClock().getClock().get(2)+">");
                    bw_deb1.newLine();
                }
            }
        }
        catch (IOException ioe)
        {
            ioe.printStackTrace();
        }
        finally
        {
            // always close the file
            if (bw_deb1 != null)
            {
                try
                {
                    bw_deb1.close();
                }
                catch (IOException ioe2)
                {
                    // just ignore it
                }
            }
        }
    }
    void printCPtQueueToFile(String inpfilename) {
        //********************************create needed file, then print candidates*******************************
        BufferedWriter bw_deb1=null;
        try
        {
            File ifilename = new File(inpfilename);
            if(!ifilename.exists()) //if file does not exist already
            {
                ifilename.getParentFile().mkdirs(); //create all necessary parent directories
                bw_deb1= new BufferedWriter(new FileWriter(ifilename));//opening file in write mode so anything already existing will be cleared
            }
            else
            {
                bw_deb1= new BufferedWriter(new FileWriter(ifilename,true));//opening file in append mode so anything already existing will not be cleared
            }
            if (!cPointQueue.isEmpty())//if there is at least one unprocessed changepoint
            {
                bw_deb1.write("Process "+id);
                bw_deb1.newLine();
                //print all the elements available in deque
                for (ChangePoint cPt : cPointQueue)
                {
                    bw_deb1.write("<" + cPt.getcPointTimestamp().getClock().get(1)+"," + cPt.getcPointTimestamp().getClock().get(2)+">");
                    bw_deb1.newLine();
                }
            }
        }
        catch (IOException ioe)
        {
            ioe.printStackTrace();
        }
        finally
        {
            // always close the file
            if (bw_deb1 != null)
            {
                try
                {
                    bw_deb1.close();
                }
                catch (IOException ioe2)
                {
                    // just ignore it
                }
            }
        }
    }
}